/**
 *
 */
#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <yices.h>

#include "io/print.h"
#include "util/str_set.h"
#include "parse/pstack.h"

const char *tag_str[NUM_TAGS] = {
    "<base>",        // TAG_BASE
    "<frame>",       // TAG_FRAME
    "<attr>",        // TAG_ATTR
    "<numeral>",     // TAG_NUMERAL
    "<sort>",        // TAG_SORT
    "<sort-constr>", // TAG_SORT_CONSTRUCTOR
    "<system>",      // TAG_SYSTEM
    "<symbol>",      // TAG_SYMBOL
    "<ident>",       // TAG_IDENTIFIER
    "<bitvec>",      // TAG_BITVEC
    "<dec>",         // TAG_DECIMAL
    "<term>",        // TAG_TERM
    "<quantifier>",        // TAG_QUANTIFIER
    "<let-binder>",        // TAG_LET_BINDER
    "<error>",       // TAG_ERROR
};

const char *frame_str[NUM_FRM_TYPES] = {
    "[no-op]",              // FRM_NOOP
    "[no-op-keep]",         // FRM_NOOP_KEEP
    "[sort]",               // FRM_SORT
    "[term]",               // FRM_TERM
    "[var-decl]",           // FRM_VAR_DECL
    "[term-bind]",          // FRM_TERM_BIND
    "[exit]",               // FRM_EXIT
    "[reset]",              // FRM_RESET
    "[assert]",             // FRM_ASSERT
    "[echo]",               // FRM_ECHO
    "[set-logic]",          // FRM_SET_LOGIC
    "[declare-enum-sort]",  // FRM_DECLARE_ENUM_SORT
    "[declare-sort]",       // FRM_DECLARE_SORT
    "[define-sort]",        // FRM_DEFINE_SORT
    "[declare-const]",      // FRM_DECLARE_CONST
    "[define-const]",       // FRM_DEFINE_CONST
    "[declare-fun]",        // FRM_DECLARE_FUN
    "[define-fun]",         // FRM_DEFINE_FUN
    "[define-system]",      // FRM_DEFINE_SYS
    "[check-system]",       // FRM_CHECK_SYS
    "[error]",              // FRM_ERROR
};

/**
 * Frames that require pushing a new var scope onto the stack:
 * - FRM_DECLARE_FUN
 * - FRM_DEFINE_FUN
 * - FRM_DEFINE_SYS
 * - FRM_CHECK_SYS
 */
bool frame_pushes_var_scope(frame_type_t frame)
{
    return frame >= FRM_DECLARE_FUN && frame <= FRM_CHECK_SYS;
}

#ifdef DEBUG_PSTACK
void pstack_print_top_frame(pstack_t *pstack)
{
    uint32_t i;
    tag_t tag;
    frame_type_t frame_type;

    frame_type = pstack->data[pstack->frame].value.frame_type;
    fprintf(stderr, "%s ", frame_str[frame_type]);

    for (i = pstack->frame + 1; i < pstack->size; ++i) {
        tag = pstack->data[i].tag;
        fprintf(stderr, "%s ", tag_str[tag]);
    }
    fprintf(stderr, "   (|frame| = %d) \n", pstack_top_frame_size(pstack));
}
#endif

void delete_pstack_elem(pstack_elem_t *elem)
{
    if (elem->tag == TAG_SYMBOL) {
        free(elem->value.str);
    }
}

void init_pstack(pstack_t *pstack, const char *filename)
{
    pstack->filename = filename;
    pstack->capacity = PSTACK_MIN_SIZE;
    pstack->data = malloc(sizeof(pstack_elem_t) * PSTACK_MIN_SIZE);
    pstack->size = 1;
    pstack->frame = 0;
    pstack->status = 0;
    pstack->cur_var_kind = LOGIC_VAR;
    init_context(&pstack->ctx);

    // Initialize bottom element
    pstack->data[0].loc = (loc_t) {0, 0};
    pstack->data[0].frame = 0;
    pstack->data[0].tag = TAG_BASE;
    pstack->data[0].value.frame_type = FRM_NOOP;
}

void delete_pstack(pstack_t *pstack)
{
    for (uint32_t i = 0; i < pstack->size; ++i) {
        delete_pstack_elem(&pstack->data[i]);
    }
    free(pstack->data);
    delete_context(&pstack->ctx);
}

void pstack_reset(pstack_t *pstack)
{
    for (uint32_t i = 0; i < pstack->size; ++i) {
        delete_pstack_elem(&pstack->data[i]);
    }
    pstack->size = 1;
    pstack->frame = 0;
    pstack->status = 0;
}

void pstack_extend(pstack_t *pstack, uint32_t size)
{
    assert(pstack->capacity < PSTACK_MAX_SIZE);
    uint32_t new_size = pstack->capacity + size;
    pstack->capacity = new_size;
    pstack->data = realloc(pstack->data, sizeof(pstack_elem_t) * new_size);
}

/**
 * Increment size and resize the stack if needed.
 */
void pstack_incr_top(pstack_t *pstack)
{
    pstack->size++;
    if (pstack->size == pstack->capacity) {
        pstack_extend(pstack, pstack->capacity / 2);
    }
}

void pstack_push_frame(pstack_t *pstack, frame_type_t ftype, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];

    elem->frame = pstack->frame;
    pstack->frame = pstack->size;
    pstack_incr_top(pstack);

    elem->tag = TAG_FRAME;
    elem->value.frame_type = ftype;
    elem->loc = loc;

    if (frame_pushes_var_scope(ftype)) {
        moxi_push_scope(&pstack->ctx);
    }
}

void pstack_push_attr(pstack_t *pstack, token_type_t attr, loc_t loc)
{
    assert(attr >= TOK_KW_INPUT && attr <= TOK_KW_UNKNOWN);

    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_ATTR;
    elem->value.tok = attr;
    elem->loc = loc;
}

void pstack_push_term(pstack_t *pstack, term_t term, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_TERM;
    elem->value.sort = term;
    elem->loc = loc;
}

void pstack_push_sort(pstack_t *pstack, sort_t sort, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_SORT;
    elem->value.sort = sort;
    elem->loc = loc;
}

void pstack_push_string(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_SYMBOL;
    uint32_t len = str->len;
    elem->value.str = malloc(len + 1 * sizeof(char));
    strncpy(elem->value.str, str->data, len + 1);
    elem->loc = loc;
}

void pstack_push_numeral(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_NUMERAL;
    // FIXME: maybe a little dangerous, we should write our own parser for
    // fixed-width ints
    elem->value.numeral = (uint32_t) strtoul(str->data, NULL, 10);
    elem->loc = loc;
}

void pstack_push_decimal(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_DECIMAL;
    uint32_t len = str->len;
    elem->value.str = malloc(len + 1 * sizeof(char));
    strncpy(elem->value.str, str->data, len + 1);
    elem->loc = loc;
}

void pstack_push_binary(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    fprintf(stderr, "pstack: pushing binary\n");
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    int status;

    // Binary constants are of the form `#b[01]+`
    // When passing to `bv64_from_str_bin`, we skip the `#b` prefix
    elem->tag = TAG_BITVEC;
    status = bv64_from_bin_str(str->data + 2, str->len - 2, &elem->value.bitvec);
    
    if (status != 0) {
        PRINT_ERROR_LOC(pstack->filename, loc, "invalid binary constant");
        longjmp(pstack->env, BAD_TERM);
    }
    elem->loc = loc;
}

void pstack_push_hex(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    int status;

    // Hexadecimal constants are of the form `#x[0-9a-fA-F]+`
    // When passing to `bv64_from_str_hex`, we skip the `#x` prefix
    elem->tag = TAG_BITVEC;
    status = bv64_from_hex_str(str->data + 2, str->len - 2, &elem->value.bitvec);
    if (status != 0) {
        PRINT_ERROR_LOC(pstack->filename, loc, "invalid hex constant");
        longjmp(pstack->env, BAD_TERM);
    }
    elem->loc = loc;
}

void pstack_push_quantifier(pstack_t *pstack, token_type_t quant, loc_t loc)
{
    assert(quant == TOK_RW_FORALL || quant == TOK_RW_EXISTS);

    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_QUANTIFIER;
    elem->value.tok = quant;
    elem->loc = loc;

    moxi_push_scope(&pstack->ctx);
}

void pstack_push_let(pstack_t *pstack, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_LET_BINDER;
    elem->value.tok = TOK_RW_LET;
    elem->loc = loc;

    moxi_push_scope(&pstack->ctx);
}

void pstack_push_error(pstack_t *pstack, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_ERROR;
    elem->loc = loc;
}

void pstack_pop(pstack_t *pstack, uint32_t n)
{
    assert(n <= pstack->size);
    uint32_t i;
    for (i = 0; i < n; ++i) {
#ifdef DEBUG_PSTACK
        fprintf(stderr, "popping: %s (%d, %d)\n", tag_str[pstack->data[pstack->size-1].tag], i, n);
#endif
        pstack->size--;
        delete_pstack_elem(&pstack->data[pstack->size]);
    }
}

void pstack_pop_frame(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "popping %d elements\n", pstack->size - pstack->frame);
#endif
    uint32_t tmp_frame = pstack->data[pstack->frame].frame;
    pstack_pop(pstack, pstack->size - pstack->frame);
    pstack->frame = tmp_frame;
}

/**
 * Pops the top frame off the stack, but keeps the elements from the frame.
 */
void pstack_pop_frame_keep(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "popping top frame, keeping elements\n");
#endif
    // Shifts all elements in the top frame down by one index in the pstack,
    // overwriting the frame tag element
    // Before: [ <frame-tag> <elem> ... <elem> <frame-tag> <elem> ... <elem> ]
    // After:  [ <frame-tag> <elem> ... <elem> <elem> ... <elem> ]
    uint32_t cur_top_frame = pstack->frame;
    uint32_t new_top_frame = pstack->data[cur_top_frame].frame;
    memmove(&pstack->data[cur_top_frame], &pstack->data[cur_top_frame + 1],
            sizeof(pstack_elem_t) * (pstack->size - cur_top_frame - 1));
    pstack->frame = new_top_frame;
    pstack->size--;
}

// Returns the `n`th element of the current frame
pstack_elem_t *get_elem(pstack_t *pstack, uint32_t n)
{
    return &pstack->data[pstack->frame + n];
}

 // Returns the tag of the `n`th element of the current frame
tag_t get_elem_tag(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].tag;
}

// Returns the token of the `n`th element of the current frame. Does not check
// the tag of the element.
token_type_t get_elem_tok(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.tok;
}

// Returns the numeral of the `n`th element of the current frame. Does not check
// the tag of the element.
uint32_t get_elem_numeral(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.numeral;
}

// Returns the symbol of the `n`th element of the current frame. Does not check
// the tag of the element.
char *get_elem_symbol(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.str;
}

// Returns the term of the `n`th element of the current frame. Does not check
// the tag of the element.
term_t get_elem_term(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.sort;
}

// Returns the sort of the `n`th element of the current frame. Does not check
// the tag of the element.
sort_t get_elem_sort(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.sort;
}

bv64_t get_elem_bv64(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.bitvec;
}

// Returns the location of the `n`th element of the current frame.
loc_t get_elem_loc(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].loc;
}

/*******************************************************************************
 * Frame checking
 ******************************************************************************/

void check_frame_size_eq(pstack_t *pstack, uint32_t n)
{
    uint32_t frame_size = pstack_top_frame_size(pstack);
    if (frame_size != n) {
        loc_t loc = pstack_top_frame_loc(pstack);
        PRINT_ERROR_LOC(pstack->filename, loc, "expected %u elements, got %u",
                        n, frame_size);
        longjmp(pstack->env, BAD_FRAME_SIZE);
    }
}

void check_frame_size_geq(pstack_t *pstack, uint32_t n)
{
    uint32_t frame_size = pstack_top_frame_size(pstack);
    if (frame_size < n) {
        loc_t loc = pstack_top_frame_loc(pstack);
        PRINT_ERROR_LOC(pstack->filename, loc,
                        "expected at least %d elements, got %d", n, frame_size);
        longjmp(pstack->env, BAD_FRAME_SIZE);
    }
}

void check_elem_tag(pstack_t *pstack, uint32_t n, tag_t tag)
{
    tag_t target = get_elem_tag(pstack, n);
    if (tag != target) {
        loc_t loc = get_elem_loc(pstack, n);
        PRINT_ERROR_LOC(pstack->filename, loc, "expected %s, got %s",
                        tag_str[tag], tag_str[target]);
        longjmp(pstack->env, BAD_TAG);
    }
}

void check_elem_sort(pstack_t *pstack, uint32_t n, sort_t sort)
{
    sort_t target = get_elem_sort(pstack, n);
    if (!yices_compatible_types(sort, target)) {
        loc_t loc = get_elem_loc(pstack, n);
        PRINT_ERROR_LOC(pstack->filename, loc, "expected sort %d, got %d", sort,
                        target);
        longjmp(pstack->env, BAD_SORT);
    }
}

/*******************************************************************************
 * Frame evaluation
 ******************************************************************************/
void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *);
void (*term_eval_table[NUM_THEORY_SYMBOLS])(pstack_t *);
term_t (*yices_bin_constructor[NUM_THEORY_SYMBOLS])(term_t, term_t);

/*****************************************
 * Sort evaluation
 ****************************************/

/**
 * ["Bool"]
 */
void eval_bool_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating Bool sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, yices_bool_type(), loc);
}

/**
 * [ "BitVec" <numeral> ]
 */
void eval_bitvec_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating BitVec sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    uint32_t width = get_elem_numeral(pstack, 2);
    sort_t sort = yices_bv_type(width);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * [ "Array" <index-sort> <elem-sort> ]
 */
void eval_array_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating Array sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_SORT);
    check_elem_tag(pstack, 3, TAG_SORT);
    sort_t index = get_elem_sort(pstack, 2);
    sort_t elem = get_elem_sort(pstack, 3);
    sort_t sort = yices_function_type1(index, elem);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * [ "Int" ]
 */
void eval_int_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating Int sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, yices_int_type(), loc);
}

/**
 * [ "Real" ]
 */
void eval_real_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating Real sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, yices_real_type(), loc);
}

/**
 * Checks that the top elements of `stack` starting at the top frame are symbols
 * that match a sort definition in `context`:
 *   - looks up symbol in context
 *   - if a built-in, then pass off to function and return
 *   - checks that num params match
 *   - constructs sort accordingly and replaces top frame
 *
 * [ <sort-symbol> <sort>* ]
 */
void eval_sort(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating sort\n");
#endif
    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);
    char *symbol = get_elem_symbol(pstack, 1);
    if (!is_active_sort(ctx, symbol)) {
        PRINT_ERROR_LOC(pstack->filename, loc, "unknown sort %s", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    theory_symbol_type_t thy_sym_type = get_theory_symbol_type(symbol);
    switch (thy_sym_type) {
    case THY_SYM_BOOL:
        eval_bool_sort(pstack);
        break;
    case THY_SYM_INT:
        eval_int_sort(pstack);
        break;
    case THY_SYM_REAL:
        eval_real_sort(pstack);
        break;
    case THY_SYM_BITVEC:
        eval_bitvec_sort(pstack);
        break;
    case THY_SYM_ARRAY:
        eval_array_sort(pstack);
        break;
    default:
    {
        // All we support currently are uninterpreted sorts with arity 0 and
        // enums
        sort_t sort = yices_get_type_by_name(symbol);
        if (sort == NULL_TYPE) {
            PRINT_ERROR_LOC(pstack->filename, loc, "unknown sort %s", symbol);
            longjmp(pstack->env, BAD_SYMBOL_KIND);
        }
        pstack_pop_frame(pstack);
        pstack_push_sort(pstack, sort, loc);
        break;
    }
    }
}

/*****************************************
 * Term evaluation
 ****************************************/

/**
 * Term evaluation starts in `eval_term` then is dispatched accordingly. For
 * literals, we handle them locally. For theory symbols, we define a function to
 * evaluate the term and use a table of function pointers to dispatch to the
 * corresponding function. For all others we use a function table stored in the
 * context via `eval_apply_term`.
 */

/**
 * Used-defined terms
 * 
 * [ <term-frame> <symbol> <term>* ]
 */
void eval_apply_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating user-defined term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 2);
    char *symbol = get_elem_symbol(pstack, 1);

    term_t app = yices_get_term_by_name(symbol);
    if (app == NULL_TERM) {
        PRINT_ERROR_LOC(pstack->filename, loc, "unknown term %s", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    if (!yices_term_is_function(app)) {
        // Then this is a constant
        check_frame_size_eq(pstack, 2);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, app, loc);
        return;
    }
    // Then `symbol` is a defined/declared function
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t term, args[nargs];

    uint32_t i;
    for (i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
    }

    term = yices_application(app, nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> <var-symbol> ]
 */
void eval_var_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var term\n");
#endif
    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    char *symbol = get_elem_symbol(pstack, 1);
    const var_table_entry_t *var = moxi_find_var(ctx, symbol);
    assert(var != NULL);

    // Primed variables must be enabled for the variable's kind in the current
    // term. Example: only primed input variables are allowed in :fairness
    if (var->is_primed) {
        if (var->kind == INPUT_VAR && !pstack->input_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc,
                            "primed input variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == OUTPUT_VAR &&
                   !pstack->output_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc,
                            "primed output variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == LOCAL_VAR && !pstack->local_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc,
                            "primed local variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == LOGIC_VAR) { // var is not a system variable
            PRINT_ERROR_LOC(pstack->filename, loc,
                            "primed variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        }
    }

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, var->term, loc);
}

/**
 * [ <term-frame> "true" ]
 */
void eval_true_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating true term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, yices_true(), loc);
}

/**
 * [ <term-frame> "false" ]
 */
void eval_false_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating false term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, yices_false(), loc);
}

/**
 * [ <term-frame> "not" <bool-term> ]
 */
void eval_not_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating not term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_not(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "=" <term> <term>+ ]
 */
void eval_eq_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating = term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t term = yices_eq(get_elem_term(pstack, 2), get_elem_term(pstack, 3));
    uint32_t i;
    for (i = 3; i < pstack_top_frame_size(pstack) - 1; ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        check_elem_tag(pstack, i + 1, TAG_TERM);
        term = yices_and2(term, yices_eq(get_elem_term(pstack, i),
                                        get_elem_term(pstack, i + 1)));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "distinct" <term> <term>+ ]
 */
void eval_distinct_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating distinct term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_distinct(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * An ite term is a conditional term that takes a boolean term followed by two
 * terms of the same sort.
 *
 * [ <term-frame> "ite" <bool-term> <term> <term> ]
 */
void eval_ite_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating ite term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 5);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    check_elem_tag(pstack, 4, TAG_TERM);
    term_t cond, lhs, rhs;
    cond = get_elem_term(pstack, 2);
    lhs = get_elem_term(pstack, 3);
    rhs = get_elem_term(pstack, 4);
    term_t term = yices_ite(cond, lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <and-op> <bool-term> <bool-term>+ ]
 */
void eval_and_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical and term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_and(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "or" <bool-term> <bool-term>+ ]
 */
void eval_or_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical or term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_or(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "xor" <bool-term> <bool-term>+ ]
 */
void eval_xor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical xor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_xor(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * Implies is right associative
 * 
 * [ <term-frame> "=>" <term> <term> ]
 */
void eval_implies_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating => term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t term = get_elem_term(pstack, 2);
    for (uint32_t i = 3; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        term = yices_implies(term, get_elem_term(pstack, i));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "+" <int-term> <int-term>+ ] 
 * [ <term-frame> "+" <real-term> <real-term>+ ]
 */
void eval_add_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating add term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_sum(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}
/**
 * [ <term-frame> "*" <int-term> <int-term>+ ]
 * [ <term-frame> "*" <real-term> <real-term>+ ]
 */
void eval_mul_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating mul term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_product(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * A minus term is either unary or multi-arity.
 * 
 * [ <term-frame> "-" <int-term> ]
 * [ <term-frame> "-" <real-term> ]
 * [ <term-frame> "-" <int-term> <int-term>+ ]
 * [ <term-frame> "-" <real-term> <real-term>+ ]
 */
void eval_minus_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating minus term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    if (pstack_top_frame_size(pstack) > 3) {
        check_frame_size_geq(pstack, 4);
        uint32_t last = pstack_top_frame_size(pstack) - 1;
        check_elem_tag(pstack, last, TAG_TERM);
        term_t term, arg;
        term = get_elem_term(pstack, last);
        for (uint32_t i = last - 1; i > 1; --i) {
            check_elem_tag(pstack, i, TAG_TERM);
            arg = get_elem_term(pstack, i);
            term = yices_sub(arg, term);
        }
        if (term == NULL_TERM) {
            yices_print_error(stderr);
            longjmp(pstack->env, BAD_TERM);
        }
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, term, loc);
        return;
    }
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_neg(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "div" <int-term> <int-term>+ ]
 */
void eval_idiv_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating idiv term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t last = pstack_top_frame_size(pstack) - 1;
    check_elem_tag(pstack, last, TAG_TERM);
    term_t term, arg;
    term = get_elem_term(pstack, last);
    for (uint32_t i = last - 1; i > 1; --i) {
        check_elem_tag(pstack, i, TAG_TERM);
        arg = get_elem_term(pstack, i);
        term = yices_idiv(arg, term);
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "/" <real-term> <real-term> ]
 */
void eval_rdiv_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating / term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t last = pstack_top_frame_size(pstack) - 1;
    check_elem_tag(pstack, last, TAG_TERM);
    term_t term, arg;
    term = get_elem_term(pstack, last);
    for (uint32_t i = last - 1; i > 1; --i) {
        check_elem_tag(pstack, i, TAG_TERM);
        arg = get_elem_term(pstack, i);
        term = yices_division(arg, term);
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "mod" <int-term> <int-term> ]
 */
void eval_mod_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating mod term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_imod(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "abs" <int-term> ]
 */
void eval_abs_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating abs term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg;
    arg = get_elem_term(pstack, 2);
    term_t term = yices_abs(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> ">" <int-term> <int-term>+ ]
 * [ <term-frame> ">" <real-term> <real-term>+ ]
 */
void eval_arith_gt_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating > term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    term_t term, arg1, arg2;
    arg1 = get_elem_term(pstack, 2);
    arg2 = get_elem_term(pstack, 3);
    term = yices_arith_gt_atom(arg1, arg2);
    for (uint32_t i = 3; i < pstack_top_frame_size(pstack) - 1; ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        check_elem_tag(pstack, i + 1, TAG_TERM);
        arg1 = get_elem_term(pstack, i);
        arg2 = get_elem_term(pstack, i + 1);
        term = yices_and2(term, yices_arith_gt_atom(arg1, arg2));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> ">=" <int-term> <int-term>+ ]
 * [ <term-frame> ">=" <real-term> <real-term>+ ]
 */
void eval_arith_ge_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating >= term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    term_t term, arg1, arg2;
    arg1 = get_elem_term(pstack, 2);
    arg2 = get_elem_term(pstack, 3);
    term = yices_arith_geq_atom(arg1, arg2);
    for (uint32_t i = 3; i < pstack_top_frame_size(pstack) - 1; ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        check_elem_tag(pstack, i + 1, TAG_TERM);
        arg1 = get_elem_term(pstack, i);
        arg2 = get_elem_term(pstack, i + 1);
        term = yices_and2(term, yices_arith_geq_atom(arg1, arg2));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "<" <int-term> <int-term>+ ]
 * [ <term-frame> "<" <real-term> <real-term>+ ]
 */
void eval_arith_lt_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating < term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    term_t term, arg1, arg2;
    arg1 = get_elem_term(pstack, 2);
    arg2 = get_elem_term(pstack, 3);
    term = yices_arith_lt_atom(arg1, arg2);
    for (uint32_t i = 3; i < pstack_top_frame_size(pstack) - 1; ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        check_elem_tag(pstack, i + 1, TAG_TERM);
        arg1 = get_elem_term(pstack, i);
        arg2 = get_elem_term(pstack, i + 1);
        term = yices_and2(term, yices_arith_lt_atom(arg1, arg2));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "<=" <int-term> <int-term>+ ]
 * [ <term-frame> "<=" <real-term> <real-term>+ ]
 */
void eval_arith_le_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating <= term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    term_t term, arg1, arg2;
    arg1 = get_elem_term(pstack, 2);
    arg2 = get_elem_term(pstack, 3);
    term = yices_arith_leq_atom(arg1, arg2);
    for (uint32_t i = 3; i < pstack_top_frame_size(pstack) - 1; ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        check_elem_tag(pstack, i + 1, TAG_TERM);
        arg1 = get_elem_term(pstack, i);
        arg2 = get_elem_term(pstack, i + 1);
        term = yices_and2(term, yices_arith_leq_atom(arg1, arg2));
    }
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "divisible" <numeral> <bool-term> ]
 */
void eval_divisible_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating divisible term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t n = yices_int64(get_elem_numeral(pstack, 2));
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_divides_atom(n, arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "concat" <bitvec-term> <bitvec-term> ]
 */
void eval_concat_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating concat term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvconcat2(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "extract" <numeral> <numeral> <bitvec-term> ]
 * 
 * ((_ extract i j) (_ BitVec m) (_ BitVec n))
 * subject to:
 * - m > i ≥ j ≥ 0
 * - n = i - j + 1
 */
void eval_bvextract_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvextract term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 5);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_NUMERAL);
    check_elem_tag(pstack, 4, TAG_TERM);
    uint32_t i, j;
    term_t arg;
    i = get_elem_numeral(pstack, 2);
    j = get_elem_numeral(pstack, 3);
    arg = get_elem_term(pstack, 4);
    term_t term = yices_bvextract(arg, j, i);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "repeat" <numeral> <bitvec-term> ]
 */
void eval_repeat_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating repeat term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    uint32_t n = get_elem_numeral(pstack, 2);
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_bvrepeat(arg, n);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "bvcomp" <bitvec-term> <bitvec-term> ]
 */
void eval_bvcomp_term(pstack_t *pstack)
{   
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvcomp term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bveq_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvredand_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvredand term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_redand(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvredor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvredor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_redor(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "bvnot" <bitvec-term> ]
 */
void eval_bvnot_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvnot term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_bvnot(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * bvand is left-associative
 * 
 * [ <term-frame> "bvand" <bitvec-term> <bitvec-term>+ ]
 */
void eval_bvand_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvand term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_bvand(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * bvor is left-associative
 * 
 * [ <term-frame> "bvor" <bitvec-term> <bitvec-term>+ ]
 */
void eval_bvor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_bvor(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "bvnand" <bitvec-term> <bitvec-term> ]
 */
void eval_bvnand_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvnand term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvnand(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "bvnor" <bitvec-term> <bitvec-term> ]
 */
void eval_bvnor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvnor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvnor(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvxor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvxor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvxor2(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvxnor_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvxnor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvxnor(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvneg_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvneg term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    term_t arg = get_elem_term(pstack, 2);
    term_t term = yices_bvneg(arg);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * bvadd is left-associative
 * 
 * [ <term-frame> "bvadd" <bitvec-term> <bitvec-term>+ ]
 */
void eval_bvadd_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvadd term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_bvsum(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsub_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsub term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsub(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * bvmul is left-associative
 * 
 * [ <term-frame> "bvmul" <bitvec-term> <bitvec-term>+ ]
 */
void eval_bvmul_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvmul term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (uint32_t i = 0; i < nargs; ++i) {
        check_elem_tag(pstack, i + 2, TAG_TERM);
        args[i] = get_elem_term(pstack, i + 2);
    }
    term_t term = yices_bvproduct(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvudiv_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvudiv term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvdiv(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvurem_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvurem term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvrem(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsdiv_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsdiv term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsdiv(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsrem_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsrem term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsrem(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsmod_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsmod term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsmod(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvshl_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvshl term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvshl(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvlshr_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvlshr term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvlshr(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvashr_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvashr term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvashr(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "zero_extend" <numeral> <bitvec-term> ]
 */
void eval_zero_extend_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating zero_extend term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    uint32_t n = get_elem_numeral(pstack, 2);
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_zero_extend(arg, n);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "sign_extend" <numeral> <bitvec-term> ]
 */
void eval_sign_extend_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating sign_extend term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    uint32_t n = get_elem_numeral(pstack, 2);
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_sign_extend(arg, n);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "rotate_left" <numeral> <bitvec-term> ]
 */
void eval_rotate_left_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating rotate_left term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    uint32_t n = get_elem_numeral(pstack, 2);
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_rotate_left(arg, n);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "rotate_right" <numeral> <bitvec-term> ]
 */
void eval_rotate_right_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating rotate_right term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_TERM);
    uint32_t n = get_elem_numeral(pstack, 2);
    term_t arg = get_elem_term(pstack, 3);
    term_t term = yices_rotate_right(arg, n);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvult_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvult term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvlt_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvule_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvule term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvle_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvugt_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvugt term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvgt_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvuge_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvuge term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvge_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvslt_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvslt term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvslt_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsle_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsle term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsle_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsgt_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsgt term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsgt_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

void eval_bvsge_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvsge term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_bvsge_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_SORT);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "select" <array-term> <index-term> ]
 */
void eval_select_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating select term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t array = get_elem_term(pstack, 2);
    term_t index = get_elem_term(pstack, 3);
    term_t term = yices_application1(array, index);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> "store" <array-term> <index-term> <elem-term> ]
 */
void eval_store_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating store term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 5);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    check_elem_tag(pstack, 4, TAG_TERM);
    term_t array = get_elem_term(pstack, 2);
    term_t index = get_elem_term(pstack, 3);
    term_t elem = get_elem_term(pstack, 4);
    term_t term = yices_update1(array, index, elem);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
}

/**
 * [ <term-frame> <bitvec> ]
 * [ <term-frame> <int> ]
 * [ <term-frame> <real> ]
 * [ <term-frame> <symbol> <term>* ]
 */
void eval_term(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating term\n");
#endif
    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);
    logic_type_t logic = ctx->logic->type;

    check_frame_size_geq(pstack, 2);
    tag_t tag = get_elem_tag(pstack, 1);
    switch (tag)
    {
    case TAG_BITVEC:
    {
        if (!logic_has_bitvectors[logic]) {
            PRINT_ERROR("bitvector literals require bitvector logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 2);
        bv64_t bitvec = get_elem_bv64(pstack, 1);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, yices_bvconst_int64(bitvec.width, bitvec.value), loc);
        break;
    }
    case TAG_NUMERAL:
    {
        if (!logic_has_ints[logic] && !logic_has_reals[logic]) {
            PRINT_ERROR("integer literals require valid logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 2);
        uint32_t value = get_elem_numeral(pstack, 1);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, yices_int64(value), loc);
        break;
    }
    case TAG_DECIMAL:
    {
        // Since decimals in yices are expected to be rationals, we just use
        // their provided parse function to convert decimal strings to yices
        // rationals.
        if (!logic_has_reals[logic]) {
            PRINT_ERROR("decimal literals require valid logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 2);
        check_elem_tag(pstack, 1, TAG_DECIMAL);
        char *decimal = get_elem_symbol(pstack, 1);
        pstack_pop_frame(pstack);
        term_t term = yices_parse_float(decimal);
        if (term == NULL_TERM) {
            yices_print_error(stderr);
            longjmp(pstack->env, BAD_TERM);
        }
        pstack_push_term(pstack, term, loc);
        break;
    }
    case TAG_QUANTIFIER:
    {
        // [ <term-frame> "forall" (<symbol> <sort>)+ <term> ]
        if (!logic_has_quantifiers[logic]) {
            PRINT_ERROR("quantifiers require quantifier-valid logic");
            longjmp(pstack->env, BAD_LOGIC);
        }

        uint32_t i;
        str_vector_t *scope = moxi_get_scope(ctx);
        const var_table_entry_t *var;
        term_t vars[scope->size];
        for (i = 0; i < scope->size; ++i) {
            var = moxi_find_var(ctx, scope->data[i]);
            vars[i] = var->term;
        }

        term_t body = get_elem_term(pstack, pstack_top_frame_size(pstack) - 1);
        term_t term = yices_forall(scope->size, vars, body);
        if (term == NULL_TERM) {
            yices_print_error(stderr);
            longjmp(pstack->env, BAD_TERM);
        }
        moxi_pop_scope(ctx);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, term, loc);        
        break;
    }
    case TAG_LET_BINDER:
    {
        // [ <term-frame> "let" (<symbol> <term>)+ <term> ]
        uint32_t last = pstack_top_frame_size(pstack) - 1;
        term_t term = get_elem_term(pstack, last);
        moxi_pop_scope(ctx);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, term, loc);  
        break;
    }
    case TAG_SYMBOL:
    {
        check_elem_tag(pstack, 1, TAG_SYMBOL);
        char *symbol = get_elem_symbol(pstack, 1);
        if (is_active_theory_term(ctx, symbol)) {
            theory_symbol_type_t sym_type = get_theory_symbol_type(symbol);
            term_eval_table[sym_type](pstack);
            break;
        }
        term_t term = yices_get_term_by_name(symbol);
        if (term == NULL_TERM) {
            PRINT_ERROR_LOC(pstack->filename, loc, "unknown term %s", symbol);
            longjmp(pstack->env, BAD_SYMBOL_KIND);
        }
        if (yices_term_constructor(term) == YICES_VARIABLE) {
            eval_var_term(pstack);
            break;
        }
        eval_apply_term(pstack);
        break;
    }
    default:
        PRINT_ERROR("bad tag");
        longjmp(pstack->env, BAD_TAG);
    }
}

void eval_bad_term(pstack_t *pstack) 
{
    char *symbol = get_elem_symbol(pstack, 1);
    PRINT_ERROR("unsupported term %s", symbol);
    longjmp(pstack->env, BAD_TERM); 
}

/*****************************************
 * Command evaluation
 ****************************************/

/**
 * [ <set-logic-frame> <symbol> ]
 */
void eval_set_logic(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: setting logic\n");
#endif
    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol = get_elem_symbol(pstack, 1);
    moxi_set_logic(ctx, symbol);
    if (ctx->status) {
        longjmp(pstack->env, BAD_LOGIC);
    }

    pstack_pop_frame(pstack);
}

/**
 * [ <define-sort-frame> <symbol> <symbol>* <sort> ]
 */
void eval_define_sort(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-sort\n");
#endif
    // TODO: will require yices_extensions.c to implement
    // (not supported by Yices' standard API, see 'yices_type_macro')
    PRINT_ERROR("define-sort not implemented");
    longjmp(pstack->env, BAD_COMMAND);
}

/**
 * [ <declare-sort-frame> <symbol> <numeral> ]
 */
void eval_declare_sort(pstack_t *pstack)
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-sort\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_NUMERAL);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol = get_elem_symbol(pstack, 1);
    uint32_t arity = get_elem_numeral(pstack, 2);

    if (arity != 0) {
        // TODO: will require yices_extensions.c to implement
        // (not supported by Yices' standard API, see 'yices_type_constructor')
        PRINT_ERROR("uninterpreted sorts with arity >0 are not supported");
        longjmp(pstack->env, BAD_SORT);
    }

    moxi_declare_sort(ctx, symbol, 0);
    if (ctx->status) {
        PRINT_ERROR("symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame(pstack);
}

/**
 * Only :init, :trans, and :inv attributes will appear here, :input, :output,
 * and :local have all been dealt with via `eval_var_decl`.
 *
 * [ <define-system-frame> <symbol> <define-system-attr>+ ]
 */
void eval_define_system(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-system\n");
#endif
    check_frame_size_geq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    moxi_context_t *ctx = &pstack->ctx;
    term_t init = yices_true();
    term_t trans = yices_true();
    term_t inv = yices_true();
    const sys_table_entry_t *subsys_type;
    char *symbol, *subsys_symbol, *subsys_type_symbol;
    uint32_t i, j, nelems;

    nelems = pstack_top_frame_size(pstack);
    symbol = get_elem_symbol(pstack, 1);

    str_vector_t *scope = moxi_get_scope(ctx);
    const var_table_entry_t *var;
    uint32_t ninput = 0, noutput = 0, nlocal = 0;
    for (j = 0; j < scope->size; ++j) {
        var = moxi_find_var(ctx, scope->data[j]);
        if (var->is_primed) {
            continue;
        } else if (var->kind == INPUT_VAR) {
            ninput++;
        } else if (var->kind == OUTPUT_VAR) {
            noutput++;
        } else if (var->kind == LOCAL_VAR) {
            nlocal++;
        }
    }
    sort_t *input, *output, *local;
    input = malloc(ninput * sizeof(sort_t));
    output = malloc(noutput * sizeof(sort_t));
    local = malloc(nlocal * sizeof(sort_t));
    uint32_t in = 0, out = 0, loc = 0;
    for (j = 0; j < scope->size; ++j) {
        var = moxi_find_var(ctx, scope->data[j]);
        if (var->is_primed) {
            continue;
        } else if (var->kind == INPUT_VAR) {
            input[in++] = yices_type_of_term(var->term);
        } else if (var->kind == OUTPUT_VAR) {
            output[out++] = yices_type_of_term(var->term);
        } else if (var->kind == LOCAL_VAR) {
            local[loc++] = yices_type_of_term(var->term);
        }
    }

    i = 2;
    while (i < nelems) {
        check_frame_size_geq(pstack, i+2);
        check_elem_tag(pstack, i, TAG_ATTR);
        token_type_t attr = get_elem_tok(pstack, i);
        switch (attr) {
        case TOK_KW_INPUT:
        case TOK_KW_OUTPUT:
        case TOK_KW_LOCAL:
            i++;
            while (i < nelems && get_elem_tag(pstack, i) == TAG_SYMBOL &&
                   get_elem_tag(pstack, i + 1) == TAG_SORT) {
                i += 2;
            }
            break;
        case TOK_KW_INIT:
            // <init-attr> <term>
            check_elem_tag(pstack, i+1, TAG_TERM);
            init = yices_and2(init, get_elem_term(pstack, i+1));
            if (init == NULL_TERM) {
                yices_print_error(stderr);
                PRINT_ERROR("bad init term");
                longjmp(pstack->env, BAD_TERM);
            }
            i += 2;
            break;
        case TOK_KW_TRANS:
            // <trans-attr> <term>
            check_elem_tag(pstack, i+1, TAG_TERM);
            trans = yices_or2(trans, get_elem_term(pstack, i+1));
            if (init == NULL_TERM) {
                yices_print_error(stderr);
                PRINT_ERROR("bad trans term");
                longjmp(pstack->env, BAD_TERM);
            }
            i += 2;
            break;
        case TOK_KW_INV:
            // <inv-attr> <term>
            check_elem_tag(pstack, i+1, TAG_TERM);
            inv = yices_and2(inv, get_elem_term(pstack, i+1));
            if (init == NULL_TERM) {
                yices_print_error(stderr);
                PRINT_ERROR("bad inv term");
                longjmp(pstack->env, BAD_TERM);
            }
            i += 2;
            break;
        case TOK_KW_SUBSYS: 
        {
            // <subsys-attr> <subsys-symbol> <subsys-type-symbol> <var-symbol>*
            // Check that:
            // - subsystem is defined
            // - number of vars match (ninput + noutput = nvars)
            // - vars are of the correct sort
            // - no input vars are mapped to subsystem's output vars
            check_frame_size_geq(pstack, i+3);
            subsys_symbol = get_elem_symbol(pstack, i+1);
            if (yices_get_term_by_name(subsys_symbol) != NULL_TERM) {
                PRINT_ERROR("symbol %s already in use", subsys_symbol);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }

            subsys_type_symbol = get_elem_symbol(pstack, i+2);
            subsys_type = moxi_find_system(ctx, subsys_type_symbol);
            if (subsys_type == NULL) {
                PRINT_ERROR("subsystem %s not defined", subsys_type_symbol);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }

            i += 3;
            uint32_t nvars = 0;
            while (i < nelems && get_elem_tag(pstack, i) == TAG_SYMBOL) {
                char *var_sym = get_elem_symbol(pstack, i);
                const var_table_entry_t *entry = moxi_find_var(ctx, var_sym);
                if (entry == NULL) {
                    PRINT_ERROR("subsys %s: variable %s not defined",
                                subsys_symbol, var_sym);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                if (nvars >= subsys_type->ninput + subsys_type->noutput) {
                    PRINT_ERROR("subsys %s: too many variables supplied",
                                subsys_symbol);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                sort_t sort = yices_type_of_term(entry->term);
                if (nvars < subsys_type->ninput &&
                    !yices_compatible_types(sort, subsys_type->input[nvars])) {
                    PRINT_ERROR("subsys %s: input variable %s has wrong sort",
                                subsys_symbol, var_sym);
                    longjmp(pstack->env, BAD_SORT);
                } else if (nvars >= subsys_type->ninput) {
                    if (!yices_compatible_types(
                            sort,
                            subsys_type->output[nvars - subsys_type->ninput])) {
                        PRINT_ERROR(
                            "subsys %s: output variable %s has wrong sort",
                            subsys_symbol, var_sym);
                        longjmp(pstack->env, BAD_SORT);
                    }
                    if (entry->kind == INPUT_VAR) {
                        PRINT_ERROR("subsys %s: input variable %s cannot be "
                                    "mapped to output",
                                    subsys_symbol, var_sym);
                        longjmp(pstack->env, BAD_SYMBOL_KIND);
                    }
                }
                nvars++;
                i++;
            }

            if (nvars != subsys_type->ninput + subsys_type->noutput) {
                PRINT_ERROR("not enough variables for subsystem %s",
                            subsys_symbol);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }

            // Add this as a dummy variable so that we don't repeat the symbol
            moxi_add_named_term(ctx, subsys_symbol, yices_new_variable(NULL_TYPE),
                         LOCAL_VAR);

            break;
        }
        default:
            PRINT_ERROR("bad attribute for define-system");
            longjmp(pstack->env, BAD_ATTR);
        }
    }

    moxi_define_system(ctx, symbol, ninput, input, noutput, output, nlocal,
                       local);
    if (ctx->status) {
        PRINT_ERROR("system %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    moxi_pop_scope(ctx);
    pstack_pop_frame(pstack);
}

/**
 * Only :assumption, :fairness, :reachable, :current, :query, and :queries
 * attributes are handled here, :input, :output, and :local have all been dealt
 * with via `eval_var_decl`.
 *
 * [ <check-system-frame> <symbol> <check-system-attr>* ]
 */
void eval_check_system(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating check-system\n");
#endif
    check_frame_size_geq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol;
    uint32_t i, j, nelems;
    const sys_table_entry_t *system;

    nelems = pstack_top_frame_size(pstack);
    symbol = get_elem_symbol(pstack, 1);
    system = moxi_find_system(ctx, symbol);
    if (system == NULL) {
        PRINT_ERROR("system %s not defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    str_vector_t *scope = moxi_get_scope(ctx);
    const var_table_entry_t *var;
    uint32_t ninput = 0, noutput = 0, nlocal = 0;
    for (j = 0; j < scope->size; ++j) {
        var = moxi_find_var(ctx, scope->data[j]);
        if (var->is_primed) {
            continue;
        } else if (var->kind == INPUT_VAR) {
            ninput++;
        } else if (var->kind == OUTPUT_VAR) {
            noutput++;
        } else if (var->kind == LOCAL_VAR) {
            nlocal++;
        }
    }

    if (ninput != system->ninput || noutput != system->noutput ||
        nlocal != system->nlocal) {
        PRINT_ERROR("incorrect number of variables for system %s", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    // Use a str_map_t as a set to store the names of formulas
    // It's good enough for fast lookups and to avoid duplicates
    str_set_t formula_names, query_names;
    init_str_set(&formula_names, 0);
    init_str_set(&query_names, 0);

    char *name;

    i = 2;
    while (i < nelems) {
        check_frame_size_geq(pstack, i+2);
        check_elem_tag(pstack, i, TAG_ATTR);
        token_type_t attr = get_elem_tok(pstack, i);
        switch (attr) {
        case TOK_KW_INPUT:
        case TOK_KW_OUTPUT:
        case TOK_KW_LOCAL:
            i++;
            while ((i < nelems) && get_elem_tag(pstack, i) == TAG_SYMBOL &&
                   get_elem_tag(pstack, i + 1) == TAG_SORT) {
                i += 2;
            }
            break;
        case TOK_KW_ASSUMPTION:
        case TOK_KW_FAIRNESS:
        case TOK_KW_REACHABLE:
        case TOK_KW_CURRENT:
            // <attr> <symbol> <term>
            check_elem_tag(pstack, i+1, TAG_SYMBOL);
            check_elem_tag(pstack, i+2, TAG_TERM);
            name = get_elem_symbol(pstack, i+1);
            if (in_str_set(&formula_names, name)) {
                PRINT_ERROR("formula %s already defined", name);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }
            str_set_add(&formula_names, name, (uint32_t) strlen(name));
            i += 3;
            break;
        case TOK_KW_QUERY:
            // <query-attr> <symbol> <symbol>*
            i++;
            check_elem_tag(pstack, i, TAG_SYMBOL);
            name = get_elem_symbol(pstack, i);
            if (in_str_set(&query_names, name)) {
                PRINT_ERROR("%s already defined", name);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }
            str_set_add(&query_names, name, (uint32_t) strlen(name));
            i++;
            while (i < nelems && get_elem_tag(pstack, i) == TAG_SYMBOL) {
                name = get_elem_symbol(pstack, i);
                if (!in_str_set(&formula_names, name)) {
                    PRINT_ERROR("formula %s not defined", name);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                i++;
            }
            break;
        case TOK_KW_QUERIES:
            // <queries-attr> (<query-attr> <symbol> <symbol>*)*
            i++;
            while (i < nelems && get_elem_tag(pstack, i) == TAG_ATTR &&
                   get_elem_tok(pstack, i) == TOK_KW_QUERY) {
                i++;
                check_elem_tag(pstack, i, TAG_SYMBOL);
                name = get_elem_symbol(pstack, i);
                if (in_str_set(&query_names, name)) {
                    PRINT_ERROR("%s already defined", name);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                str_set_add(&query_names, name, (uint32_t) strlen(name));
                i++;
                while (i < nelems && get_elem_tag(pstack, i) == TAG_SYMBOL) {
                    name = get_elem_symbol(pstack, i);
                    if (!in_str_set(&formula_names, name)) {
                        PRINT_ERROR("formula %s not defined", name);
                        longjmp(pstack->env, BAD_SYMBOL_KIND);
                    }
                    i++;
                }
            }
            break;
        default:
            PRINT_ERROR("bad attribute for check-system");
            longjmp(pstack->env, BAD_ATTR);
        }
    }

    delete_str_set(&formula_names);
    delete_str_set(&query_names);

    moxi_pop_scope(ctx);
    pstack_pop_frame(pstack);
}

/**
 *  [ <declare-enum-sort-frame> <symbol> <symbol>+ ] 
 */
void eval_declare_enum_sort(pstack_t *pstack) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-enum-sort\n");
#endif
    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    char *sort_symbol = get_elem_symbol(pstack, 1);
    uint32_t nvalues = pstack_top_frame_size(pstack) - 2;
    char **enum_symbols = malloc(nvalues * sizeof(char *));

    uint32_t i;
    for (i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_SYMBOL);
        enum_symbols[i-2] = get_elem_symbol(pstack, i);
    }

    moxi_declare_enum_sort(ctx, sort_symbol, nvalues, enum_symbols);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol already defined");
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame(pstack);
}

/**
 * [ <declare-const-frame> <symbol> <sort> ]
 */
void eval_declare_const(pstack_t *pstack) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-const\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);

    moxi_declare_fun(ctx, symbol, 0, NULL, sort);
    if (ctx->status) {
        PRINT_ERROR("symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame(pstack);
}

/**
 * [ <define-const-frame> <symbol> <sort> <term> ]
 */
void eval_define_const(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-const\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);
    check_elem_tag(pstack, 3, TAG_TERM);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);
    term_t term = get_elem_term(pstack, 3);

    if (!yices_compatible_types(sort, yices_type_of_term(term))) {
        PRINT_ERROR_LOC(pstack->filename, loc, "sort mismatch");
        longjmp(pstack->env, BAD_SORT);
    }

    moxi_define_fun(ctx, symbol, 0, NULL, sort, term);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame(pstack);
}

/**
 * A define-fun command is used to define a new function symbol in the current
 * context. The list of sorts represents the rank of the function, with the last
 * sort being the return sort.
 * 
 * FIXME: check that symbol is not already defined
 *
 * [ <define-fun-frame> <symbol> (<symbol> <sort>)* <sort> <term> ]
 * [ <define-fun-frame> <symbol> <symbol> <sort> <symbol> <sort> <sort> <term> ]
 */
void eval_define_fun(pstack_t *pstack) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-fun\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_geq(pstack, 4);
    uint32_t nargs, i;
    nargs = (pstack_top_frame_size(pstack) - 4) / 2;
    sort_t *args, ret;
    term_t body;
    char *symbol;
    moxi_context_t *ctx = &pstack->ctx;

    args = malloc(nargs * sizeof(sort_t));

    /**
     * frame[0]: define-fun frame
     * frame[1]: function symbol
     * frame[2]: symbol of first argument (ignore)
     * frame[3]: sort of first argument 
     * ...
     * frame[2+((nargs-1)*2)]: symbol of last argument (ignore)
     * frame[3+((nargs-1)*2)]: sort of last argument
     * frame[2+(nargs*2)]: sort of return value
     * frame[3+(nargs*2)]: term
     * 
     * Construct `args` array as follows:
     * args[0] = frame[3]
     * args[1] = frame[5]
     * ...
     * args[nargs-1] = frame[3+((nargs-1)*2)]
     */
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    for (i = 3; i < 3 + (nargs * 2); i = i + 2) {
        check_elem_tag(pstack, i, TAG_SORT);
        args[(i-3)/2] = get_elem_sort(pstack, i);
    }
    check_elem_tag(pstack, 2 + (nargs * 2), TAG_SORT);
    check_elem_tag(pstack, 3 + (nargs * 2), TAG_TERM);

    symbol = get_elem_symbol(pstack, 1);
    ret = get_elem_sort(pstack, 2 + (nargs * 2));
    body = get_elem_term(pstack, 3 + (nargs * 2));

    if (!yices_compatible_types(ret, yices_type_of_term(body))) {
        PRINT_ERROR_LOC(pstack->filename, loc, "return sort mismatch");
        longjmp(pstack->env, BAD_SORT);
    }

    moxi_define_fun(ctx, symbol, nargs, args, ret, body);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    free(args);
    moxi_pop_scope(ctx);
    pstack_pop_frame(pstack);
}

/**
 * A declare-fun command is used to declare a new uninterpreted function symbol
 * in the current context. The list of sorts represents the rank of the
 * function, with the last sort being the return sort.
 *
 * [ <declare-fun-frame> <symbol> <sort>+ ]
 */
void eval_declare_fun(pstack_t *pstack)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-fun\n");
#endif
    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);

    if (!logic_has_uf[ctx->logic->type]) {
        PRINT_ERROR_LOC(pstack->filename, loc, "uninterpreted functions not supported in current logic");
        longjmp(pstack->env, BAD_LOGIC);
    }

    check_frame_size_geq(pstack, 3);
    uint32_t nargs, i;
    nargs = pstack_top_frame_size(pstack) - 3;
    sort_t *args, ret;
    char *symbol;

    args = malloc(nargs * sizeof(sort_t));

    /**
     * frame[1]: function symbol
     * frame[2]: sort of first argument 
     * ...
     * frame[2+(nargs-1)]: sort of last argument
     * frame[2+nargs]: sort of return value
     */
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    for (i = 2; i < nargs + 2; ++i) {
        check_elem_tag(pstack, i, TAG_SORT);
        args[i-2] = get_elem_sort(pstack, i);
    }
    check_elem_tag(pstack, nargs + 2, TAG_SORT);

    symbol = get_elem_symbol(pstack, 1);
    ret = get_elem_sort(pstack, nargs + 2);

    moxi_declare_fun(ctx, symbol, nargs, args, ret);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    free(args);
    moxi_pop_scope(ctx);
    pstack_pop_frame(pstack);
}

/**
 * For variable declarations, we add the variable to the context and push the
 * sort to the stack.
 *
 * We do not pop the elements of the frame since we may need to refer to the
 * symbols later. If we pop the full frame, then the symbols will be freed, and
 * we will not be able to use them. This just saves us from having to copy them.
 *
 * [ <var-decl-frame> <symbol> <sort> ]
 */
void eval_var_decl(pstack_t *pstack) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var decl\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    moxi_context_t *ctx = &pstack->ctx;
    loc_t loc = pstack_top_frame_loc(pstack);

    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);
    term_t var = yices_new_variable(sort);
    if (var == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }

    moxi_add_named_term(ctx, symbol, var, pstack->cur_var_kind);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame_keep(pstack);
}

/**
 * [ <term-binder-frame> <symbol> <term> ]
 */
void eval_term_binder(pstack_t *pstack) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating term binder\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_TERM);

    moxi_context_t *ctx = &pstack->ctx;
    char *symbol = get_elem_symbol(pstack, 1);
    term_t term = get_elem_term(pstack, 2);

    moxi_add_named_term(ctx, symbol, term, LOGIC_VAR);
    if (ctx->status) {
        PRINT_ERROR("symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame_keep(pstack);
}

void eval_noop_pop_frame(pstack_t *pstack) 
{
    pstack_pop_frame(pstack);
}

void eval_noop(pstack_t *pstack) 
{ 
    pstack_pop_frame_keep(pstack);
}

void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *) = {
    eval_noop_pop_frame,    // FRM_NOOP,
    eval_noop,              // FRM_NOOP_KEEP,
    eval_sort,              // FRM_SORT,
    eval_term,              // FRM_TERM,
    eval_var_decl,          // FRM_VAR_DECL,
    eval_term_binder,       // FRM_TERM_BIND,
    eval_noop_pop_frame,    // FRM_EXIT,
    eval_noop_pop_frame,    // FRM_RESET,
    eval_noop_pop_frame,    // FRM_ASSERT,
    eval_noop_pop_frame,    // FRM_ECHO,
    eval_set_logic,         // FRM_SET_LOGIC,
    eval_declare_enum_sort, // FRM_DECLARE_ENUM_SORT,
    eval_declare_sort,      // FRM_DECLARE_SORT,
    eval_define_sort,       // FRM_DEFINE_SORT,
    eval_declare_const,     // FRM_DECLARE_CONST,
    eval_define_const,      // FRM_DEFINE_CONST,
    eval_declare_fun,       // FRM_DECLARE_FUN,
    eval_define_fun,        // FRM_DEFINE_FUN,
    eval_define_system,     // FRM_DEFINE_SYS,
    eval_check_system,      // FRM_CHECK_SYS,
    eval_noop_pop_frame     // FRM_ERROR
};

void (*term_eval_table[NUM_THEORY_SYMBOLS])(pstack_t *) = {
    eval_bad_term,       // BOOL
    eval_true_term,      // TRUE
    eval_false_term,     // FALSE
    eval_not_term,       // NOT
    eval_implies_term,   // IMPLIES
    eval_and_term,       // AND
    eval_or_term,        // OR
    eval_xor_term,       // XOR
    eval_eq_term,        // EQ
    eval_distinct_term,  // DISTINCT
    eval_ite_term,       // ITE
    eval_bad_term,       // ARRAY
    eval_select_term,    // SELECT
    eval_store_term,     // STORE
    eval_bad_term,       // INT
    eval_bad_term,       // REAL
    eval_minus_term,     // MINUS
    eval_add_term,       // PLUS
    eval_mul_term,       // TIMES
    eval_idiv_term,      // IDIV
    eval_rdiv_term,      // RDIV
    eval_arith_le_term,  // LE
    eval_arith_lt_term,  // LT
    eval_arith_ge_term,  // GE
    eval_arith_gt_term,  // GT
    eval_divisible_term, // DIVISIBLE
    eval_mod_term,       // MOD
    eval_abs_term,       // ABS
    eval_bad_term,       // TO_REAL
    eval_bad_term,       // TO_INT
    eval_bad_term,       // BITVEC
    eval_concat_term,    // CONCAT
    eval_bvextract_term, // EXTRACT
    eval_repeat_term,    // REPEAT
    eval_bvcomp_term,    // BVCOMP
    eval_bvredand_term,  // BVREDAND
    eval_bvredor_term,   // BVREDOR
    eval_bvnot_term,     // BVNOT
    eval_bvand_term,     // BVAND
    eval_bvor_term,      // BVOR
    eval_bvnand_term,    // BVNAND
    eval_bvnor_term,     // BVNOR
    eval_bvxor_term,     // BVXOR
    eval_bvxnor_term,    // BVXNOR
    eval_bvneg_term,     // BVNEG
    eval_bvadd_term,     // BVADD
    eval_bvsub_term,     // BVSUB
    eval_bvmul_term,     // BVMUL
    eval_bvudiv_term,    // BVUDIV
    eval_bvurem_term,    // BVUREM
    eval_bvsdiv_term,    // BVSDIV
    eval_bvsrem_term,    // BVSREM
    eval_bvsmod_term,    // BVSMOD
    eval_bvshl_term,     // BVSHL
    eval_bvlshr_term,    // BVLSHR
    eval_bvashr_term,    // BVASHR
    eval_zero_extend_term,  // ZERO_EXTEND
    eval_sign_extend_term,  // SIGN_EXTEND
    eval_rotate_left_term,  // ROTATE_LEFT
    eval_rotate_right_term, // ROTATE_RIGHT
    eval_bvult_term, // BVULT
    eval_bvule_term, // BVULE
    eval_bvugt_term, // BVUGT
    eval_bvuge_term, // BVUGE
    eval_bvslt_term, // BVSLT
    eval_bvsle_term, // BVSLE
    eval_bvsgt_term, // BVSGT
    eval_bvsge_term, // BVSGE
    eval_bad_term,   // UNKNOWN
};

void pstack_eval_frame(pstack_t *pstack)
{
    pstack_elem_t *top;
    frame_type_t top_frame_type;

    top = pstack_top_frame(pstack);
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating frame idx=%d\n", pstack->frame);
    pstack_print_top_frame(pstack);
#endif
    top_frame_type = top->value.frame_type;
    frame_eval_table[top_frame_type](pstack);
}
