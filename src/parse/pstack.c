/**
 *
 */
#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "io/print.h"
#include "moxi/context.h"
#include "parse/pstack.h"

const char *tag_str[NUM_TAGS] = {
    "<base>",        // TAG_BASE
    "<frame>",       // TAG_FRAME
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

void delete_pstack_elem(pstack_elem_t *elem)
{
    if (elem->tag == TAG_SYMBOL) {
        free(elem->value.symbol);
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

void pstack_push_symbol(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    size_t len = str->len + 1;

    elem->tag = TAG_SYMBOL;
    elem->value.symbol = malloc(sizeof(char) * len + 1);
    strncpy(elem->value.symbol, str->data, len + 1);
    elem->loc = loc;
}

void pstack_push_numeral(pstack_t *pstack, char_buffer_t *str, loc_t loc)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->size];
    pstack_incr_top(pstack);

    int64_t numeral = atol(str->data);

    elem->tag = TAG_NUMERAL;
    elem->value.numeral = numeral;
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
    pstack_pop(pstack, 1);
    memmove(&pstack->data[cur_top_frame], &pstack->data[cur_top_frame + 1],
            sizeof(pstack_elem_t) * (pstack->size - cur_top_frame));
    pstack->frame = new_top_frame;
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
    return pstack->data[pstack->frame + n].value.symbol;
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

void check_frame_size_gte(pstack_t *pstack, uint32_t n)
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

/*******************************************************************************
 * Frame evaluation
 ******************************************************************************/

/*****************************************
 * Sort evaluation
 ****************************************/

/**
 * ["Bool"]
 */
void eval_bool_sort(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating bool sort\n");

    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, bool_sort, loc);
}

/**
 * ["BitVec", N]
 */
void eval_bitvec_sort(pstack_t *pstack, context_t *ctx)
{
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 2, TAG_NUMERAL);

    uint64_t width = get_elem_numeral(pstack, 2);
    sort_t sort = get_bitvec_sort(&ctx->sort_table, width);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * ["Array", <index-sort>, <elem-sort>]
 */
void eval_array_sort(pstack_t *pstack, context_t *ctx)
{
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_SORT);
    check_elem_tag(pstack, 3, TAG_SORT);

    sort_t index = get_elem_sort(pstack, 2);
    sort_t elem = get_elem_sort(pstack, 3);
    sort_t sort = get_array_sort(&ctx->sort_table, index, elem);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

/**
 * ["Int"]
 */
void eval_int_sort(pstack_t *pstack, context_t *ctx)
{
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, int_sort, loc);
}

/**
 * ["Real"]
 */
void eval_real_sort(pstack_t *pstack, context_t *ctx)
{
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, real_sort, loc);
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
void eval_sort(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating sort\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    char *name = get_elem_symbol(pstack, 1);
    symbol_kind_t symbol_kind = context_find(ctx, name);

    if (symbol_kind != SYM_KIND_SORT) {
        PRINT_ERROR_LOC(pstack->filename, loc, "unknown sort '%s'", name);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    const symbol_t *symbol = get_symbol(name);
    symbol_type_t sym_type = (symbol == NULL ? SYM_SYMBOL : symbol->type);
    switch (sym_type) {
    case SYM_BOOL:
        eval_bool_sort(pstack, ctx);
        break;
    case SYM_INT:
        eval_int_sort(pstack, ctx);
        break;
    case SYM_REAL:
        eval_real_sort(pstack, ctx);
        break;
    case SYM_BITVEC:
        eval_bitvec_sort(pstack, ctx);
        break;
    case SYM_ARRAY:
        eval_array_sort(pstack, ctx);
        break;
    default:
        // TODO: user-defined sort
        PRINT_ERROR_LOC(pstack->filename, loc, "unkown sort '%s'", name);
        longjmp(pstack->env, BAD_SORT);
        break;
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
 * Used-defined functions
 * 
 * [ <symbol> <term>* ]
 */
void eval_apply_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating user-defined term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    char *name = get_elem_symbol(pstack, 1);

    symbol_kind_t symbol_kind = context_find(ctx, name);
    if (symbol_kind != SYM_KIND_TERM) {
        PRINT_ERROR_LOC(pstack->filename, loc, "unknown term '%s'", name);
        longjmp(pstack->env, BAD_SYMBOL_KIND);
    }

    rank_t *rank;
    rank = str_map_find(&ctx->fun_table, name);

    size_t nargs = pstack_top_frame_size(pstack) - 1;
    if (nargs != rank->len - 1) {
        PRINT_ERROR_LOC(pstack->filename, loc,
                        "expected %lu arguments, got %lu", rank->len - 1,
                        nargs);
        longjmp(pstack->env, BAD_TERM);
    }

    size_t i;
    sort_t expected, actual;
    for (i = 0; i < rank->len - 1; ++i) {
        expected = rank->sorts[i];
        actual = get_elem_sort(pstack, i + 2);
        if (expected != actual) {
            PRINT_ERROR_LOC(pstack->filename, loc,
                            "bad sort at index %lu (%u, %u)", i, expected,
                            actual);
            longjmp(pstack->env, BAD_SORT);
        }
    }

    sort_t ret_sort = rank->sorts[rank->len - 1];
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, ret_sort, loc);
}

/**
 * [ "var-symbol" ]
 */
void eval_var_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var term\n");
#endif

    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    char *symbol = get_elem_symbol(pstack, 1);

    var_table_entry_t *var = context_find_var_symbol(ctx, symbol);
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, var->sort, loc);
}

/**
 * [ "true" ]
 */
void eval_true_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating true term\n");
#endif

    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, bool_sort, loc);
}

/**
 * [ "false" ]
 */
void eval_false_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating false term\n");
#endif

    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 1);

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, bool_sort, loc);
}

/**
 * [ "not" <bool-term> ]
 */
void eval_not_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating not term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 2, TAG_TERM);

    term_t t = get_elem_term(pstack, 2);
    if (!is_bool_sort(&ctx->sort_table, t)) {
        longjmp(pstack->env, BAD_SORT);
    }

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, bool_sort, loc);
}

/**
 * Logical binary operators include: `and`, `or`, `xor`, and `=>`
 * 
 * [ <logic-bin-op> <bool-term> <bool-term> ]
 */
void eval_logic_bin_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating logical binary term\n");
#endif

    loc_t loc = pstack_top_frame_loc(pstack);
    char *op = get_elem_symbol(pstack, 1);

    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);

    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    if (!is_bool_sort(&ctx->sort_table, lhs) || !is_bool_sort(&ctx->sort_table, rhs)) {
        PRINT_ERROR("'%s' term requires bool arguments", op);
        longjmp(pstack->env, BAD_SORT);
    }

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, bool_sort, loc);
}

/**
 * [ "extract" <numeral> <numeral> <bitvec-term> ]
 * 
 * ((_ extract i j) (_ BitVec m) (_ BitVec n))
 * subject to:
 * - m > i ≥ j ≥ 0
 * - n = i - j + 1
 */
void eval_bvextract_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating bvextract term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_NUMERAL);
    check_elem_tag(pstack, 4, TAG_TERM);

    uint32_t i, j, m, n;
    term_t t;

    i = get_elem_numeral(pstack, 2);
    j = get_elem_numeral(pstack, 3);
    t = get_elem_term(pstack, 4);

    if (i < j) {
        PRINT_ERROR("bad extract indices");
        longjmp(pstack->env, BAD_BVEXTRACT_IDX);
    }
    if (j < 0) {
        PRINT_ERROR("bad extract indices");
        longjmp(pstack->env, BAD_BVEXTRACT_IDX);
    }
    if (!is_bitvec_sort(&ctx->sort_table, t)) {
        PRINT_ERROR("extract requires bitvector argument");
        longjmp(pstack->env, BAD_SORT);
    }
    m = get_bitvec_width(&ctx->sort_table, t);
    if (m <= i) {
        PRINT_ERROR("bad extract indices");
        longjmp(pstack->env, BAD_SORT);
    }    
    n = i - j + 1;
    term_t new = get_bitvec_sort(&ctx->sort_table, n);
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, loc);
}

/**
 * Arithmetic binary operators include `+`, `-`, `*`, and `/`
 * 
 * [ <arith-bin-op> <int-term> <int-term>+ ]
 * [ <arith-bin-op> <real-term> <real-term>+ ]
 */
void eval_arith_bin_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating arithmetic binary term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    char *op = get_elem_symbol(pstack, 1);
    term_t t;

    check_frame_size_gte(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);

    t = get_elem_term(pstack, 2);
    bool is_int = true;
    if (is_int_sort(&ctx->sort_table, t)) {
        is_int = true;
    } else if (is_real_sort(&ctx->sort_table, t)) {
        is_int = false;
    } else {
        PRINT_ERROR_LOC(pstack->filename, loc, "'%s' term requires int or real arguments", op);
        longjmp(pstack->env, BAD_SORT);
    }

    for (size_t i = 3; i < pstack_top_frame_size(pstack); ++i) {
        check_elem_tag(pstack, i, TAG_TERM);
        t = get_elem_term(pstack, i);
        if (is_int ? !is_int_sort(&ctx->sort_table, t) : !is_real_sort(&ctx->sort_table, t)) {
            PRINT_ERROR_LOC(pstack->filename, loc, "'%s' term requires int or real arguments", op);
            longjmp(pstack->env, BAD_SORT);
        }
    }

    term_t new = is_int ? int_sort : real_sort;
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, loc);
}

/**
 * Arithmetic relational operators include `<`, `>`, `<=`, and `>=`
 * 
 * [ <arith-rel-op> <int-term> <int-term> ]
 * [ <arith-rel-op> <real-term> <real-term> ]
 */
void eval_arith_rel_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating arithmetic relational term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    char *op = get_elem_symbol(pstack, 1);

    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);

    term_t lhs, rhs;
    lhs = get_elem_term(pstack, 2);
    rhs = get_elem_term(pstack, 3);
    
    if (
        (is_int_sort(&ctx->sort_table, lhs) && is_int_sort(&ctx->sort_table, rhs)) || 
        (is_real_sort(&ctx->sort_table, lhs) && is_real_sort(&ctx->sort_table, rhs))
    ) {
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, bool_sort, loc);
    } else {
        PRINT_ERROR_LOC(pstack->filename, loc, "'%s' term requires int or real arguments", op);
        longjmp(pstack->env, BAD_SORT);
    }

    pstack_pop_frame(pstack);
    pstack_push_term(pstack, bool_sort, loc);
}

/**
 * [ <bitvec> ]
 * [ <int> ]
 * [ <real> ]
 * [ <symbol> <term>* ]
 */
void eval_term(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating term\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);
    logic_type_t logic = ctx->logic->type;

    check_frame_size_gte(pstack, 1);
    tag_t tag = get_elem_tag(pstack, 1);
    switch (tag)
    {
    case TAG_BITVEC:
    {
        if (!logic_has_bitvectors[logic]) {
            PRINT_ERROR("bitvector literals require bitvector logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        uint64_t width;
        check_frame_size_eq(pstack, 2);
        width = get_elem_numeral(pstack, 2);
        sort_t bv_sort = get_bitvec_sort(&ctx->sort_table, width);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, bv_sort, loc);
        break;
    }
    case TAG_NUMERAL:
    {
        if (!logic_has_ints[logic]) {
            PRINT_ERROR("int literals require int logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 1);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, int_sort, loc);
        break;
    }
    case TAG_DECIMAL:
    {
        if (!logic_has_reals[logic]) {
            PRINT_ERROR("real literals require real logic");
            longjmp(pstack->env, BAD_LOGIC);
        }
        check_frame_size_eq(pstack, 1);
        pstack_pop_frame(pstack);
        pstack_push_term(pstack, real_sort, loc);
        break;
    }
    case TAG_SYMBOL:
    {
        char *name = get_elem_symbol(pstack, 1);
        symbol_kind_t symbol_kind = context_find(ctx, name);

        if (symbol_kind == SYM_KIND_VARIABLE) {
            eval_var_term(pstack, ctx);
            return;
        }

        if (symbol_kind != SYM_KIND_TERM) {
            PRINT_ERROR("unknown term '%s' (%d)", name, symbol_kind);
            longjmp(pstack->env, BAD_SYMBOL_KIND);
        }

        const symbol_t *symbol = get_symbol(name);
        symbol_type_t sym_type = (symbol == NULL ? SYM_SYMBOL : symbol->type);
        term_eval_table[sym_type](pstack, ctx);
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
 * [ <symbol> ]
 */
void eval_set_logic(pstack_t *pstack, context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: setting logic\n");
#endif
    check_frame_size_eq(pstack, 1);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    char *symbol = get_elem_symbol(pstack, 1);
    size_t len = strlen(symbol);
    if (!set_current_logic(ctx, symbol, len)) {
        longjmp(pstack->env, BAD_LOGIC);
    }

    pstack_pop_frame(pstack);
}

void eval_define_system(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_COMMAND); }
void eval_check_system(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_COMMAND); }
void eval_define_sort(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_COMMAND); }
void eval_declare_sort(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_COMMAND); }
void eval_declare_enum_sort(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_COMMAND); }

void eval_declare_const(pstack_t *pstack, context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-const\n");
#endif
    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);

    context_add_const_symbol(ctx, symbol, sort);
    context_reset_var_symbols(ctx);
    pstack_pop_frame(pstack);
}

/**
 * [ <symbol> <sort> <term> ]
 */
void eval_define_const(pstack_t *pstack, context_t *ctx) 
{ 
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-const\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_eq(pstack, 3);
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

    context_add_const_symbol(ctx, symbol, sort);
    context_reset_var_symbols(ctx);
    pstack_pop_frame(pstack);
}

/**
 * A define-fun command is used to define a new function symbol in the current
 * context. The list of sorts represents the rank of the function, with the last
 * sort being the return sort.
 * 
 * FIXME: check that symbol is not already defined
 *
 * [ <symbol> <sort>+ <term> ]
 */
void eval_define_fun(pstack_t *pstack, context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating define-fun\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    check_frame_size_gte(pstack, 3);
    uint32_t nargs, i;
    nargs = pstack_top_frame_size(pstack) - 3;

    /**
     * frame[1]: function symbol
     * frame[2]: sort of first argument 
     * ...
     * frame[2+(nargs-1)]: sort of last argument
     * frame[2+nargs]: sort of return value
     * frame[3+nargs]: term
     */
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    for (i = 2; i < nargs + 3; ++i) {
        check_elem_tag(pstack, i, TAG_SORT);
    }
    check_elem_tag(pstack, nargs + 3, TAG_TERM);

    char *symbol;
    sort_t *sort_list;

    sort_list = malloc(sizeof(sort_t) * (nargs + 1));
    symbol = get_elem_symbol(pstack, 1);
    for (i = 2; i < nargs + 3; ++i) {
        sort_list[i-2] = get_elem_sort(pstack, i);
    }
    sort_list[nargs] = get_elem_sort(pstack, nargs + 2);

    term_t term = get_elem_term(pstack, nargs + 3);
    if (sort_list[nargs] != term) {
        PRINT_ERROR_LOC(pstack->filename, loc, "return sort mismatch");
        longjmp(pstack->env, BAD_SORT);
    }

    rank_t *rank = malloc(sizeof(rank_t));
    rank->sorts = sort_list;
    rank->len = nargs + 1;

    context_add_fun_symbol(ctx, symbol, rank);
    context_reset_var_symbols(ctx);
    pstack_pop_frame(pstack);
}

/**
 * A declare-fun command is used to declare a new uninterpreted function symbol
 * in the current context. The list of sorts represents the rank of the
 * function, with the last sort being the return sort.
 *
 * [ <symbol> <sort>+ ]
 */
void eval_declare_fun(pstack_t *pstack, context_t *ctx)
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating declare-fun\n");
#endif
    loc_t loc = pstack_top_frame_loc(pstack);

    if (!logic_has_uf[ctx->logic->type]) {
        PRINT_ERROR_LOC(pstack->filename, loc, "uninterpreted functions not supported in current logic");
        longjmp(pstack->env, BAD_LOGIC);
    }

    check_frame_size_gte(pstack, 2);
    uint32_t nargs, i;
    nargs = pstack_top_frame_size(pstack) - 2;

    /**
     * frame[1]: function symbol
     * frame[2]: sort of first argument 
     * ...
     * frame[2+(nargs-1)]: sort of last argument
     * frame[2+nargs]: sort of return value
     */
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    for (i = 2; i < nargs + 3; ++i) {
        check_elem_tag(pstack, i, TAG_SORT);
    }

    char *symbol;
    sort_t *sort_list;

    sort_list = malloc(sizeof(sort_t) * (nargs + 1));
    symbol = get_elem_symbol(pstack, 1);
    for (i = 2; i < nargs + 3; ++i) {
        sort_list[i-2] = get_elem_sort(pstack, i);
    }
    sort_list[nargs] = get_elem_sort(pstack, nargs + 2);

    rank_t *rank = malloc(sizeof(rank_t));
    rank->sorts = sort_list;
    rank->len = nargs + 1;

    context_add_fun_symbol(ctx, symbol, rank);
    context_reset_var_symbols(ctx);
    pstack_pop_frame(pstack);
}


/**
 * For variable declarations, we add the variable to the context and push the
 * sort to the stack.
 *
 * [ <symbol> <sort> ]
 */
void eval_var_decl(pstack_t *pstack, context_t *ctx) 
{
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating var decl\n");
#endif

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    loc_t loc = pstack_top_frame_loc(pstack);

    char *symbol = get_elem_symbol(pstack, 1);
    sort_t sort = get_elem_sort(pstack, 2);
    context_add_var_symbol(ctx, symbol, LOGIC_VAR, sort); // FIXME: change from fixed logic var

    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, loc);
}

void eval_term_binder(pstack_t *pstack, context_t *ctx) { longjmp(pstack->env, BAD_TERM); }

/**
 * Pops the current frame from the pstack.
 */
void eval_noop_pop_frame(pstack_t *pstack, context_t *ctx) 
{
    pstack_pop_frame(pstack);
}

/**
 * 
 */
void eval_noop(pstack_t *pstack, context_t *ctx) 
{ 
    pstack_pop_frame_keep(pstack);
}

void eval_bad_term(pstack_t *pstack, context_t *ctx) 
{
    char *name = get_elem_symbol(pstack, 1);
    PRINT_ERROR("unsupported term %s", name);
    longjmp(pstack->env, BAD_TERM); 
}

void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, context_t *) = {
    eval_noop,             // FRM_NOOP,
    eval_sort,             // FRM_SORT,
    eval_term,             // FRM_TERM,
    eval_noop_pop_frame,   // FRM_EXIT,
    eval_noop_pop_frame,   // FRM_RESET,
    eval_noop_pop_frame,   // FRM_ASSERT,
    eval_noop_pop_frame,   // FRM_ECHO,
    eval_set_logic,        // FRM_SET_LOGIC,
    eval_noop_pop_frame,   // FRM_DEFINE_SYS,
    eval_noop_pop_frame,   // FRM_CHECK_SYS,
    eval_noop_pop_frame,   // FRM_DECLARE_SORT,
    eval_noop_pop_frame,   // FRM_DECLARE_ENUM_SORT,
    eval_noop_pop_frame,   // FRM_DECLARE_CONST,
    eval_declare_fun,      // FRM_DECLARE_FUN,
    eval_noop_pop_frame,   // FRM_DEFINE_SORT,
    eval_define_const,     // FRM_DEFINE_CONST,
    eval_define_fun,       // FRM_DEFINE_FUN,
    eval_var_decl,         // FRM_VAR_DECL,
    eval_noop_pop_frame,   // FRM_TERM_BIND,
    eval_noop_pop_frame    // FRM_ERROR
};

void (*term_eval_table[NUM_SYMBOLS])(pstack_t *, context_t *) = {
    eval_bad_term, // BOOL
    eval_true_term, // TRUE
    eval_false_term, // FALSE
    eval_not_term, // NOT
    eval_bad_term, // IMPLIES
    eval_logic_bin_term, // AND
    eval_bad_term, // OR
    eval_bad_term, // XOR
    eval_bad_term, // EQ
    eval_bad_term, // DISTINCT
    eval_bad_term, // ITE
    eval_bad_term, // ARRAY
    eval_bad_term, // SELECT
    eval_bad_term, // STORE
    eval_bad_term, // INT
    eval_bad_term, // REAL
    eval_bad_term, // MINUS
    eval_arith_bin_term, // PLUS
    eval_bad_term, // TIMES
    eval_bad_term, // DIVIDES
    eval_arith_rel_term, // LE
    eval_arith_rel_term, // LT
    eval_arith_rel_term, // GE
    eval_arith_rel_term, // GT
    eval_bad_term, // DIV
    eval_bad_term, // MOD
    eval_bad_term, // ABS
    eval_bad_term, // TO_REAL
    eval_bad_term, // TO_INT
    eval_bad_term, // BITVEC
    eval_bad_term, // CONCAT
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
    eval_apply_term, // SYMBOL
    eval_bad_term, // UNKNOWN
};

void pstack_eval_frame(pstack_t *pstack, context_t *ctx)
{
    pstack_elem_t *top;
    frame_type_t top_frame_type;

    top = pstack_top_frame(pstack);
#ifdef DEBUG_PSTACK
    fprintf(stderr, "pstack: evaluating frame idx=%d\n", pstack->frame);
    pstack_print_frame(pstack);
#endif
    top_frame_type = top->value.frame_type;
    frame_eval_table[top_frame_type](pstack, ctx);
}

#ifdef DEBUG_PSTACK
void pstack_print_frame(pstack_t *pstack)
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