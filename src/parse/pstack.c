/**
 *
 */
#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <yices.h>

#include "io/print.h"
#include "util/str_set.h"
#include "parse/pstack.h"

const char *tag_str[NUM_TAGS] = {
    "<base>",        // TAG_BASE
    "<frame>",       // TAG_FRAME
    "<attr>",       // TAG_ATTR
    "<numeral>",     // TAG_NUMERAL
    "<sort>",        // TAG_SORT
    "<sort-constr>", // TAG_SORT_CONSTRUCTOR
    "<system>",      // TAG_SYSTEM
    "<symbol>",      // TAG_SYMBOL
    "<ident>",       // TAG_IDENTIFIER
    "<bitvec>",      // TAG_BITVEC
    "<dec>",         // TAG_DECIMAL
    "<term>",        // TAG_TERM
    "<error>",       // TAG_ERROR
};

const char *frame_str[NUM_FRM_TYPES] = {
    "[no-op]",              // FRM_NOOP
    "[no-op-keep]",         // FRM_NOOP_KEEP
    "[push-scope]",         // FRM_PUSH_SCOPE
    "[sort]",               // FRM_SORT
    "[term]",               // FRM_TERM
    "[exit]",               // FRM_EXIT
    "[reset]",              // FRM_RESET
    "[assert]",             // FRM_ASSERT
    "[echo]",               // FRM_ECHO
    "[set-logic]",          // FRM_SET_LOGIC
    "[define-system]",      // FRM_DEFINE_SYS
    "[check-system]",       // FRM_CHECK_SYS
    "[declare-sort]",       // FRM_DECLARE_SORT
    "[declare-enum-sort]",  // FRM_DECLARE_ENUM_SORT
    "[declare-const]",      // FRM_DECLARE_CONST
    "[declare-fun]",        // FRM_DECLARE_FUN
    "[define-sort]",        // FRM_DEFINE_SORT
    "[define-const]",       // FRM_DEFINE_CONST
    "[define-fun]",         // FRM_DEFINE_FUN
    "[var-decl]",           // FRM_VAR_DECL
    "[term-bind]",          // FRM_TERM_BIND
    "[error]",              // FRM_ERROR
};

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
    size_t new_size = pstack->capacity + size;
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
}

void pstack_push_attr(pstack_t *pstack, token_type_t attr, loc_t loc)
{
    assert(attr >= TOK_KW_INPUT && attr <= TOK_KW_UNKNOWN);

    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_ATTR;
    elem->value.attr = attr;
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
    size_t len = str->len;
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
    elem->value.numeral = atol(str->data);
    elem->loc = loc;
}

void pstack_push_decimal(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    elem->tag = TAG_DECIMAL;
    size_t len = str->len;
    elem->value.str = malloc(len + 1 * sizeof(char));
    strncpy(elem->value.str, str->data, len + 1);
    elem->loc = loc;
}

void pstack_push_binary(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    // Binary constants are of the form `#b[01]+`
    elem->tag = TAG_BITVEC;
    elem->value.bitvec.value = strtol(str->data, NULL, 2);
    elem->value.bitvec.width = str->len - 2;
    elem->loc = loc;
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

// Returns the attribute of the `n`th element of the current frame. Does not check
// the tag of the element.
token_type_t get_elem_attr(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.attr;
}

// Returns the numeral of the `n`th element of the current frame. Does not check
// the tag of the element.
uint64_t get_elem_numeral(pstack_t *pstack, uint32_t n)
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

// Returns the sort of the `n`th element of the current frame. Does not check
// the tag of the element.
bv64_lit_t get_elem_bv64_lit(pstack_t *pstack, uint32_t n)
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
    if (sort != target) {
        loc_t loc = get_elem_loc(pstack, n);
        PRINT_ERROR_LOC(pstack->filename, loc, "expected sort %d, got %d", sort,
                        target);
        longjmp(pstack->env, BAD_SORT);
    }
}

/*******************************************************************************
 * Frame evaluation
 ******************************************************************************/

/*****************************************
 * Sort evaluation
 ****************************************/

/**
 * ["Bool"]
 */
void eval_bool_sort(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_bitvec_sort(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating BitVec sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    uint64_t width = get_elem_numeral(pstack, 2);
    sort_t sort = yices_bv_type(width);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * [ "Array" <index-sort> <elem-sort> ]
 */
void eval_array_sort(pstack_t *pstack, moxi_context_t *ctx)
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
    sort_t sort = yices_tuple_type2(index, elem);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * [ "Int" ]
 */
void eval_int_sort(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_real_sort(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_sort(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    char *symbol = get_elem_symbol(pstack, 1);
    if (!is_active_sort(ctx, symbol)) {
        PRINT_ERROR_LOC(pstack->filename, loc, "unknown sort %s", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    theory_symbol_type_t thy_sym_type = get_theory_symbol_type(ctx, symbol);
    switch (thy_sym_type) {
    case THY_SYM_BOOL:
        eval_bool_sort(pstack, ctx);
        break;
    case THY_SYM_INT:
        eval_int_sort(pstack, ctx);
        break;
    case THY_SYM_REAL:
        eval_real_sort(pstack, ctx);
        break;
    case THY_SYM_BITVEC:
        eval_bitvec_sort(pstack, ctx);
        break;
    case THY_SYM_ARRAY:
        eval_array_sort(pstack, ctx);
        break;
    default:
    {
        // All we support currently are uninterpreted sorts with arity 0
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
void eval_apply_term(pstack_t *pstack, moxi_context_t *ctx)
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

    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
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
void eval_var_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 2);
    char *symbol = get_elem_symbol(pstack, 1);
    const var_table_entry_t *var = moxi_find_var(ctx, symbol);
    assert(var != NULL);

    // Primed variables must be:
    // - local or output variables
    // - in a :trans term (pstack->enable_next_vars will be set in parser)
    size_t len = strlen(symbol);
    if (var->is_primed) {
        if (var->kind == INPUT_VAR && !pstack->input_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc, "primed input variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == OUTPUT_VAR && !pstack->output_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc, "primed output variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == LOCAL_VAR && !pstack->local_next_vars_enabled) {
            PRINT_ERROR_LOC(pstack->filename, loc, "primed local variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        } else if (var->kind == LOGIC_VAR) { // var is not a system variable
            PRINT_ERROR_LOC(pstack->filename, loc, "primed variable %s not allowed", symbol);
            longjmp(pstack->env, BAD_TERM);
        }
    }

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, var->var, loc);
}

/**
 * [ <term-frame> "true" ]
 */
void eval_true_term(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_false_term(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_not_term(pstack_t *pstack, moxi_context_t *ctx)
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
 * [ <term-frame> "=" <term> <term> ]
 */
void eval_eq_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating = term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_eq(lhs, rhs);
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
void eval_distinct_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating distinct term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
    }
    check_elem_tag(pstack, pstack_top_frame_size(pstack), TAG_TERM);
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
void eval_ite_term(pstack_t *pstack, moxi_context_t *ctx)
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
void eval_and_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical and term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 3);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
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
void eval_or_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical or term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
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
void eval_xor_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical xor term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
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
 * [ <term-frame> "=>" <term> <term> ]
 */
void eval_implies_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating => term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_implies(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
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
void eval_bvextract_term(pstack_t *pstack, moxi_context_t *ctx)
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
 * [ <term-frame> "+" <int-term> <int-term>+ ]
 * [ <term-frame> "+" <real-term> <real-term>+ ]
 */
void eval_add_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating add term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_geq(pstack, 4);
    uint32_t nargs = pstack_top_frame_size(pstack) - 2;
    term_t args[nargs];
    for (size_t i = 2; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        args[i-2] = get_elem_term(pstack, i);
    }
    term_t term = yices_sum(nargs, args);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        PRINT_ERROR("yices error code: %d", yices_error_code());
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
 * [ <term-frame> "-" <int-term> <int-term> ]
 * [ <term-frame> "-" <real-term> <real-term> ]
 */
void eval_minus_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating minus term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    if (pstack_top_frame_size(pstack) > 3) {
         // then this is a binary minus
        check_frame_size_eq(pstack, 4);
        check_elem_tag(pstack, 2, TAG_TERM);
        check_elem_tag(pstack, 3, TAG_TERM);
        term_t lhs, rhs;
        lhs = get_elem_term(pstack, 2);
        rhs = get_elem_term(pstack, 3);
        term_t term = yices_sub(lhs, rhs);
        if (term == NULL_TERM) {
            yices_print_error(stderr);
            longjmp(pstack->env, BAD_TERM);
        }
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, term, loc);
        return;
    }
    // else treat as unary operator
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
 * Arithmetic relational operators include `<`, `>`, `<=`, and `>=`
 * 
 * [ <term-frame> <arith-rel-op> <int-term> <int-term> ]
 * [ <term-frame> <arith-rel-op> <real-term> <real-term> ]
 */
void eval_arith_gt_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating arithmetic relational term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);
    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    term_t term = yices_arith_gt_atom(lhs, rhs);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, term, loc);
    return;
}

/**
 * [ <term-frame> <bitvec> ]
 * [ <term-frame> <int> ]
 * [ <term-frame> <real> ]
 * [ <term-frame> <symbol> <term>* ]
 */
void eval_term(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating term\n");
#endif
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
        bv64_lit_t bitvec = get_elem_bv64_lit(pstack, 1);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, yices_bvconst_int64(bitvec.width, bitvec.value), loc);
        break;
    }
    case TAG_NUMERAL:
    {
        if (!logic_has_ints[logic]) {
            PRINT_ERROR("Int literals require Int logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 2);
        uint64_t value = get_elem_numeral(pstack, 1);
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
            PRINT_ERROR("Real literals require Real logic");
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
    case TAG_SYMBOL:
    {
        char *symbol = get_elem_symbol(pstack, 1);
        if (is_active_theory_term(ctx, symbol)) {
            theory_symbol_type_t thy_sym_type = get_theory_symbol_type(ctx, symbol);
            term_eval_table[thy_sym_type](pstack, ctx);
            break;
        }
        term_t term = yices_get_term_by_name(symbol);
        if (term == NULL_TERM) {
            PRINT_ERROR_LOC(pstack->filename, loc, "unknown term %s", symbol);
            longjmp(pstack->env, BAD_SYMBOL_KIND);
        }
        if (yices_term_constructor(term) == YICES_VARIABLE) {
            eval_var_term(pstack, ctx);
            break;
        }
        eval_apply_term(pstack, ctx);
        break;
    }
    default:
        PRINT_ERROR("bad tag");
        longjmp(pstack->env, BAD_TAG);
    }
}

/*****************************************
 * Command evaluation
 ****************************************/

/**
 * [ <set-logic-frame> <symbol> ]
 */
void eval_set_logic(pstack_t *pstack, moxi_context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: setting logic\n");
#endif
    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

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
void eval_define_sort(pstack_t *pstack, moxi_context_t *ctx) 
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
void eval_declare_sort(pstack_t *pstack, moxi_context_t *ctx)
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-sort\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_NUMERAL);

    char *symbol = get_elem_symbol(pstack, 1);
    uint64_t arity = get_elem_numeral(pstack, 2);

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
void eval_define_system(pstack_t *pstack, moxi_context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-system\n");
#endif
    check_frame_size_geq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    term_t init = yices_true();
    term_t trans = yices_true();
    term_t inv = yices_true();
    sys_table_entry_t *subsys_type;
    char *symbol, *subsys_symbol, *subsys_type_symbol;
    uint32_t i, j;

    symbol = get_elem_symbol(pstack, 1);

    str_vector_t *scope = moxi_get_scope(ctx);
    var_table_entry_t *var;
    size_t ninput = 0, noutput = 0, nlocal = 0;
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
    size_t in = 0, out = 0, loc = 0;
    for (j = 0; j < scope->size; ++j) {
        var = moxi_find_var(ctx, scope->data[j]);
        if (var->is_primed) {
            continue;
        } else if (var->kind == INPUT_VAR) {
            input[in++] = yices_type_of_term(var->var);
        } else if (var->kind == OUTPUT_VAR) {
            output[out++] = yices_type_of_term(var->var);
        } else if (var->kind == LOCAL_VAR) {
            local[loc++] = yices_type_of_term(var->var);
        }
    }

    i = 2;
    while (i < pstack_top_frame_size(pstack)) {
        check_frame_size_geq(pstack, i+2);
        check_elem_tag(pstack, i, TAG_ATTR);
        token_type_t attr = get_elem_attr(pstack, i);
        switch (attr) {
        case TOK_KW_INPUT:
        case TOK_KW_OUTPUT:
        case TOK_KW_LOCAL:
            i++;
            while(get_elem_tag(pstack, i) == TAG_SYMBOL && get_elem_tag(pstack, i+1) == TAG_SORT) { i += 2; }
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
            size_t nvars = 0;
            while(get_elem_tag(pstack, i) == TAG_SYMBOL) { 
                char *var = get_elem_symbol(pstack, i);
                var_table_entry_t *entry = moxi_find_var(ctx, var);
                if (entry == NULL) {
                    PRINT_ERROR("subsys %s: variable %s not defined", subsys_symbol, var);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                if (nvars >= subsys_type->ninput + subsys_type->noutput) {
                    PRINT_ERROR("subsys %s: too many variables supplied", subsys_symbol);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                sort_t sort = yices_type_of_term(entry->var);
                if (nvars < subsys_type->ninput && sort != subsys_type->input[nvars]) {
                    PRINT_ERROR("subsys %s: input variable %s has wrong sort", subsys_symbol, var);
                    longjmp(pstack->env, BAD_SORT);
                } else if (nvars >= subsys_type->ninput) {
                    if (sort != subsys_type->output[nvars - subsys_type->ninput]) {
                        PRINT_ERROR("subsys %s: output variable %s has wrong sort", subsys_symbol, var);
                        longjmp(pstack->env, BAD_SORT);
                    }
                    if (entry->kind == INPUT_VAR) {
                        PRINT_ERROR("subsys %s: input variable %s cannot be mapped to output", subsys_symbol, var);
                        longjmp(pstack->env, BAD_SYMBOL_KIND);
                    }
                }
                nvars++;
                i++;
            }

            if (nvars != subsys_type->ninput + subsys_type->noutput) {
                PRINT_ERROR("not enough variables for subsystem %s", subsys_symbol);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }

            // Add this as a dummy variable so that we don't repeat the symbol
            moxi_add_var(ctx, subsys_symbol, yices_new_variable(NULL_TYPE), LOCAL_VAR);
            
            break;
        }
        default:
            PRINT_ERROR("bad attribute for define-system");
            longjmp(pstack->env, BAD_ATTR);
        }
    }

    moxi_define_system(ctx, symbol, ninput, input, noutput, output, nlocal,
                       local, init, trans, inv);
    if (ctx->status) {
        PRINT_ERROR("system %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    moxi_pop_scope(ctx);
    pstack_pop_frame(pstack);
}

static void default_delete_entry_(void *entry) { }

/**
 * Only :assumption, :fairness, :reachable, :current, :query, and :queries
 * attributes are handled here, :input, :output, and :local have all been dealt
 * with via `eval_var_decl`.
 *
 * [ <check-system-frame> <symbol> <check-system-attr>* ]
 */
void eval_check_system(pstack_t *pstack, moxi_context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating check-system\n");
#endif
    check_frame_size_geq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    char *symbol;
    uint32_t i, j;
    sys_table_entry_t *system;

    symbol = get_elem_symbol(pstack, 1);
    system = moxi_find_system(ctx, symbol);
    if (system == NULL) {
        PRINT_ERROR("system %s not defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    str_vector_t *scope = moxi_get_scope(ctx);
    var_table_entry_t *var;
    size_t ninput = 0, noutput = 0, nlocal = 0;
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

    if (ninput != system->ninput || noutput != system->noutput || nlocal != system->nlocal) {
        PRINT_ERROR("incorrect number of variables for system %s", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    // Use a str_map_t as a set to store the names of formulas
    // It's good enough for fast lookups and to avoid duplicates
    str_set_t formula_names, query_names;
    init_str_set(&formula_names, 0);
    init_str_set(&query_names, 0);

    char *name;
    term_t term;

    i = 2;
    while (i < pstack_top_frame_size(pstack)) {
        check_frame_size_geq(pstack, i+2);
        check_elem_tag(pstack, i, TAG_ATTR);
        token_type_t attr = get_elem_attr(pstack, i);
        switch (attr) {
        case TOK_KW_INPUT:
        case TOK_KW_OUTPUT:
        case TOK_KW_LOCAL:
            i++;
            while(get_elem_tag(pstack, i) == TAG_SYMBOL && get_elem_tag(pstack, i+1) == TAG_SORT) { i += 2; }
            break;
        case TOK_KW_ASSUMPTION:
        case TOK_KW_FAIRNESS:
        case TOK_KW_REACHABLE:
        case TOK_KW_CURRENT:
            // <attr> <symbol> <term>
            check_elem_tag(pstack, i+1, TAG_SYMBOL);
            check_elem_tag(pstack, i+2, TAG_TERM);
            name = get_elem_symbol(pstack, i+1);
            term = get_elem_term(pstack, i+2);
            if (in_str_set(&formula_names, name)) {
                PRINT_ERROR("formula %s already defined", name);
                longjmp(pstack->env, BAD_SYMBOL_KIND);
            }
            str_set_add(&formula_names, name, strlen(name));
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
            str_set_add(&query_names, name, strlen(name));
            i++;
            while(get_elem_tag(pstack, i) == TAG_SYMBOL) { 
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
            while (get_elem_tag(pstack, i) == TAG_ATTR && get_elem_attr(pstack, i) == TOK_KW_QUERY) {
                i++;
                check_elem_tag(pstack, i, TAG_SYMBOL);
                name = get_elem_symbol(pstack, i);
                if (in_str_set(&query_names, name)) {
                    PRINT_ERROR("%s already defined", name);
                    longjmp(pstack->env, BAD_SYMBOL_KIND);
                }
                str_set_add(&query_names, name, strlen(name));
                i++;
                while(get_elem_tag(pstack, i) == TAG_SYMBOL) { 
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

void eval_declare_enum_sort(pstack_t *pstack, moxi_context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-enum-sort\n");
#endif
    PRINT_ERROR("declare-enum-sort not implemented");
    longjmp(pstack->env, BAD_COMMAND);
}

/**
 * [ <declare-const-frame> <symbol> <sort> ]
 */
void eval_declare_const(pstack_t *pstack, moxi_context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-const\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

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
void eval_define_const(pstack_t *pstack, moxi_context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-const\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);
    check_elem_tag(pstack, 3, TAG_TERM);

    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);
    term_t term = get_elem_term(pstack, 3);

    if (sort != term) {
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
void eval_define_fun(pstack_t *pstack, moxi_context_t *ctx) 
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

    if (ret != yices_type_of_term(body)) {
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
void eval_declare_fun(pstack_t *pstack, moxi_context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-fun\n");
#endif
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
void eval_var_decl(pstack_t *pstack, moxi_context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var decl\n");
#endif
    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    loc_t loc = pstack_top_frame_loc(pstack);

    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);
    term_t var = yices_new_variable(sort);
    if (var == NULL_TERM) {
        yices_print_error(stderr);
        longjmp(pstack->env, BAD_TERM);
    }

    moxi_add_var(ctx, symbol, var, pstack->cur_var_kind);
    if (ctx->status) {
        PRINT_ERROR_LOC(pstack->filename, loc, "symbol %s already defined", symbol);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    pstack_pop_frame_keep(pstack);
}

void eval_term_binder(pstack_t *pstack, moxi_context_t *ctx) { longjmp(pstack->env, BAD_TERM); }

/**
 * [ <push-scope-frame> ]
 */
void eval_push_scope(pstack_t *pstack, moxi_context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: pushing new scope\n");
#endif
    moxi_push_scope(ctx);
    pstack_pop_frame(pstack);
}

void eval_noop_pop_frame(pstack_t *pstack, moxi_context_t *ctx) 
{
    pstack_pop_frame(pstack);
}

void eval_noop(pstack_t *pstack, moxi_context_t *ctx) 
{ 
    pstack_pop_frame_keep(pstack);
}

void eval_bad_term(pstack_t *pstack, moxi_context_t *ctx) 
{
    char *symbol = get_elem_symbol(pstack, 1);
    PRINT_ERROR("unsupported term %s", symbol);
    longjmp(pstack->env, BAD_TERM); 
}

void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, moxi_context_t *) = {
    eval_noop_pop_frame,    // FRM_NOOP,
    eval_noop,              // FRM_NOOP_KEEP,
    eval_push_scope,        // FRM_PUSH_SCOPE,
    eval_sort,              // FRM_SORT,
    eval_term,              // FRM_TERM,
    eval_noop_pop_frame,    // FRM_EXIT,
    eval_noop_pop_frame,    // FRM_RESET,
    eval_noop_pop_frame,    // FRM_ASSERT,
    eval_noop_pop_frame,    // FRM_ECHO,
    eval_set_logic,         // FRM_SET_LOGIC,
    eval_define_system,     // FRM_DEFINE_SYS,
    eval_check_system,      // FRM_CHECK_SYS,
    eval_declare_sort,      // FRM_DECLARE_SORT,
    eval_declare_enum_sort, // FRM_DECLARE_ENUM_SORT,
    eval_declare_const,     // FRM_DECLARE_CONST,
    eval_declare_fun,       // FRM_DECLARE_FUN,
    eval_define_sort,       // FRM_DEFINE_SORT,
    eval_define_const,      // FRM_DEFINE_CONST,
    eval_define_fun,        // FRM_DEFINE_FUN,
    eval_var_decl,          // FRM_VAR_DECL,
    eval_term_binder,       // FRM_TERM_BIND,
    eval_noop_pop_frame     // FRM_ERROR
};

void (*term_eval_table[NUM_THEORY_SYMBOLS])(pstack_t *, moxi_context_t *) = {
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
    eval_bad_term,       // SELECT
    eval_bad_term,       // STORE
    eval_bad_term,       // INT
    eval_bad_term,       // REAL
    eval_minus_term,     // MINUS
    eval_add_term,       // PLUS
    eval_bad_term,       // TIMES
    eval_bad_term,       // DIVIDES
    eval_bad_term,       // LE
    eval_bad_term,       // LT
    eval_bad_term,       // GE
    eval_arith_gt_term,  // GT
    eval_bad_term,       // DIV
    eval_bad_term,       // MOD
    eval_bad_term,       // ABS
    eval_bad_term,       // TO_REAL
    eval_bad_term,       // TO_INT
    eval_bad_term,       // BITVEC
    eval_bad_term,       // CONCAT
    eval_bvextract_term, // EXTRACT
    eval_bad_term, // REPEAT
    eval_bad_term, // BVCOMP
    eval_bad_term, // BVREDAND
    eval_bad_term, // BVREDOR
    eval_bad_term, // BVNOT
    eval_bad_term, // BVAND
    eval_bad_term, // BVOR
    eval_bad_term, // BVNAND
    eval_bad_term, // BVNOR
    eval_bad_term, // BVXOR
    eval_bad_term, // BVXNOR
    eval_bad_term, // BVNEG
    eval_bad_term, // BVADD
    eval_bad_term, // BVSUB
    eval_bad_term, // BVMUL
    eval_bad_term, // BVUDIV
    eval_bad_term, // BVUREM
    eval_bad_term, // BVSDIV
    eval_bad_term, // BVSREM
    eval_bad_term, // BVSMOD
    eval_bad_term, // BVSHL
    eval_bad_term, // BVLSHR
    eval_bad_term, // BVASHR
    eval_bad_term, // ZERO_EXTEND
    eval_bad_term, // SIGN_EXTEND
    eval_bad_term, // ROTATE_LEFT
    eval_bad_term, // ROTATE_RIGHT
    eval_bad_term, // BVULT
    eval_bad_term, // BVULE
    eval_bad_term, // BVUGT
    eval_bad_term, // BVUGE
    eval_bad_term, // BVSLT
    eval_bad_term, // BVSLE
    eval_bad_term, // BVSGT
    eval_bad_term, // BVSGE
    eval_bad_term, // UNKNOWN
};

void pstack_eval_frame(pstack_t *pstack, moxi_context_t *ctx)
{
    pstack_elem_t *top;
    frame_type_t top_frame_type;

    top = pstack_top_frame(pstack);
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating frame idx=%d\n", pstack->frame);
    pstack_print_top_frame(pstack);
#endif
    top_frame_type = top->value.frame_type;
    frame_eval_table[top_frame_type](pstack, ctx);
}
