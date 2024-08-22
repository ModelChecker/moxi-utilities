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
    "<int>",         // TAG_INT
    "<dec>",         // TAG_DECIMAL
    "<term>",        // TAG_TERM
    "<error>",       // TAG_ERROR
};

const char *frame_str[NUM_FRM_TYPES] = {
    "[no-op]", // FRM_NOOP,
    "[sort]", // FRM_SORT,
    "[term]", // FRM_TERM,
    "[define-system]", // FRM_DEFINE_SYS,
    "[check-system]", // FRM_CHECK_SYS,
    "[declare-sort]", // FRM_DECLARE_SORT,
    "[declare-enum-sort]", // FRM_DECLARE_ENUM_SORT,
    "[declare-const]", // FRM_DECLARE_CONST,
    "[declare-fun]", // FRM_DECLARE_FUN,
    "[define-sort]", // FRM_DEFINE_SORT,
    "[define-const]", // FRM_DEFINE_CONST,
    "[define-fun]", // FRM_DEFINE_FUN,
    "[var-decl]", // FRM_VAR_DECL,
    "[term-bind]", // FRM_TERM_BIND,
    "[error]", // FRM_ERROR
};

void delete_pstack_elem(pstack_elem_t *elem)
{
    switch (elem->tag) {
    case TAG_SYMBOL:
        free(elem->value.symbol);
        break;
    default:
        break;
    }
}

void init_pstack(pstack_t *pstack)
{
    pstack->size = PSTACK_MIN_SIZE;
    pstack->data = malloc(sizeof(pstack_elem_t) * PSTACK_MIN_SIZE);
    pstack->top = 1;
    pstack->frame = 0;
    pstack->status = 0;

    // Initialize bottom element
    pstack->data[0].col = 0;
    pstack->data[0].lineno = 0;
    pstack->data[0].frame = 0;
    pstack->data[0].tag = TAG_BASE;
    pstack->data[0].value.frame_type = FRM_NOOP;
}

void delete_pstack(pstack_t *pstack)
{
    for (uint32_t i = 0; i < pstack->top; ++i) {
        delete_pstack_elem(&pstack->data[i]);
    }
    free(pstack->data);
}

void pstack_reset(pstack_t *pstack)
{
    for (uint32_t i = 0; i < pstack->top; ++i) {
        delete_pstack_elem(&pstack->data[i]);
    }
    pstack->top = 1;
    pstack->frame = 0;
    pstack->status = 0;
}

void pstack_extend(pstack_t *pstack, uint32_t size)
{
    assert(pstack->size < PSTACK_MAX_SIZE);
    size_t new_size = pstack->size + size;
    pstack->size = new_size;
    pstack->data = realloc(pstack->data, sizeof(pstack_elem_t) * new_size);
}

/**
 * Increment top and resize the stack if needed.
 */
void pstack_incr_top(pstack_t *pstack)
{
    pstack->top++;
    if (pstack->top == pstack->size) {
        pstack_extend(pstack, pstack->size / 2);
    }
}

void pstack_push_frame(pstack_t *pstack, frame_type_t ftype, uint32_t lineno,
                       uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];

    elem->frame = pstack->frame;
    pstack->frame = pstack->top;
    pstack_incr_top(pstack);

    elem->tag = TAG_FRAME;
    elem->value.frame_type = ftype;
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_push_term(pstack_t *pstack, term_t *term, uint32_t lineno,
                      uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];
    pstack_incr_top(pstack);

    elem->tag = TAG_TERM;
    elem->value.sort = term;
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_push_sort(pstack_t *pstack, sort_t *sort, uint32_t lineno,
                      uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];
    pstack_incr_top(pstack);

    elem->tag = TAG_SORT;
    elem->value.sort = sort;
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_push_symbol(pstack_t *pstack, string_buffer_t *str, uint32_t lineno,
                        uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];
    pstack_incr_top(pstack);

    size_t len = str->len + 1;

    elem->tag = TAG_SYMBOL;
    elem->value.symbol = malloc(sizeof(char *) * len);
    strncpy(elem->value.symbol, str->data, len);
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_push_numeral(pstack_t *pstack, string_buffer_t *str,
                         uint32_t lineno, uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];
    pstack_incr_top(pstack);

    int64_t numeral = atol(str->data);

    elem->tag = TAG_NUMERAL;
    elem->value.numeral = numeral;
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_push_error(pstack_t *pstack, uint32_t lineno, uint32_t col)
{
    pstack_elem_t *elem;
    elem = &pstack->data[pstack->top];
    pstack_incr_top(pstack);

    elem->tag = TAG_ERROR;
    elem->lineno = lineno;
    elem->col = col;
}

void pstack_pop(pstack_t *pstack, uint32_t n)
{
    assert(n <= pstack->top);
    uint32_t i;
    for (i = 0; i < n; ++i) {
        fprintf(stderr, "popping: %s (%d, %d)\n", tag_str[pstack->data[pstack->top-1].tag], i, n);
        pstack->top--;
        delete_pstack_elem(&pstack->data[pstack->top]);
    }
}

void pstack_pop_frame(pstack_t *pstack)
{
    fprintf(stderr, "popping %d elements\n", pstack->top - pstack->frame);
    uint32_t tmp_frame = pstack->data[pstack->frame].frame;
    pstack_pop(pstack, pstack->top - pstack->frame);
    pstack->frame = tmp_frame;
}

/**
 * Returns the `n`th element of the current frame
 */
pstack_elem_t *pstack_get_elem(pstack_t *pstack, uint32_t n)
{
    return &pstack->data[pstack->frame + n];
}

/**
 * Returns the tag of the `n`th element of the current frame
 */
tag_t pstack_get_elem_tag(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].tag;
}

/**
 * Returns the numeral of the `n`th element of the current frame. Does not check
 * the tag of the element.
 */
uint64_t pstack_get_elem_numeral(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.numeral;
}

/**
 * Returns the symbol of the `n`th element of the current frame. Does not check
 * the tag of the element.
 */
char *pstack_get_elem_symbol(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.symbol;
}

/**
 * Returns the term of the `n`th element of the current frame. Does not check
 * the tag of the element.
 */
term_t *pstack_get_elem_term(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.sort;
}

/**
 * Returns the sort of the `n`th element of the current frame. Does not check
 * the tag of the element.
 */
sort_t *pstack_get_elem_sort(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].value.sort;
}

/**
 * Returns the lineno of the `n`th element of the current frame.
 */
uint32_t pstack_get_elem_lineno(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].lineno;
}

/**
 * Returns the col of the `n`th element of the current frame.
 */
uint32_t pstack_get_elem_col(pstack_t *pstack, uint32_t n)
{
    return pstack->data[pstack->frame + n].col;
}

/**
 * In case of error:
 * - pop current frame
 * - push error
 * - return error code
 * - in parse.c if we see an error then clear pstack and return with error
 */
void pstack_error(pstack_t *pstack)
{
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;
    pstack_pop_frame(pstack);
    pstack_push_error(pstack, lineno, col);
    pstack->status = 1;
}

/*******************************************************************************
 * Frame checking
 ******************************************************************************/

void check_frame_size_eq(pstack_t *pstack, uint32_t n)
{
    if (pstack->status)
        return;
    if (pstack_top_frame_size(pstack) != n) {
        pstack_error(pstack);
    }
}

void check_frame_size_gte(pstack_t *pstack, uint32_t n)
{
    if (pstack->status)
        return;
    if (pstack_top_frame_size(pstack) < n) {
        pstack_error(pstack);
    }
}

void check_elem_tag(pstack_t *pstack, uint32_t idx, tag_t tag) { }

/*******************************************************************************
 * Frame evaluation
 ******************************************************************************/

/*****************************************
 * Sort evaluation
 ****************************************/

/**
 * ["Bool"]
 */
void pstack_eval_bool_sort(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating bool sort\n");

    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);

    sort_t *sort = new_bool_sort();
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

/**
 * ["BitVec", N]
 */
void pstack_eval_bitvec_sort(pstack_t *pstack, context_t *ctx)
{
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 2, TAG_NUMERAL);

    uint64_t width = pstack_get_elem_numeral(pstack, 2);
    sort_t *sort = new_bitvec_sort(width);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

/**
 * ["Array", <index-sort>, <elem-sort>]
 */
void pstack_eval_array_sort(pstack_t *pstack, context_t *ctx)
{
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_SORT);
    check_elem_tag(pstack, 3, TAG_SORT);

    sort_t *index = pstack_get_elem_sort(pstack, 2);
    sort_t *elem = pstack_get_elem_sort(pstack, 3);
    sort_t *sort = new_array_sort(index, elem);
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

/**
 * ["Int"]
 */
void pstack_eval_int_sort(pstack_t *pstack, context_t *ctx)
{
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);

    sort_t *sort = new_int_sort();
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

/**
 * ["Real"]
 */
void pstack_eval_real_sort(pstack_t *pstack, context_t *ctx)
{
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);

    sort_t *sort = new_real_sort();
    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

/**
 * Checks that the top elements of `stack` starting at the top frame are symbols
 * that match a sort definition in `context`:
 *   - looks up symbol in context
 *   - if a built-in, then pass off to function and return
 *   - checks that num params match
 *   - constructs sort accordingly and replaces top frame
 *
 * [ <sort-symbol>, <sort>* ]
 */
void pstack_eval_sort(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating sort\n");

    char *symbol = pstack_get_elem_symbol(pstack, 1);

    if (!strcmp(symbol, "Bool")) {
        pstack_eval_bool_sort(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "BitVec")) {
        pstack_eval_bitvec_sort(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "Array")) {
        pstack_eval_array_sort(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "Int")) {
        pstack_eval_int_sort(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "Real")) {
        pstack_eval_real_sort(pstack, ctx);
        return;
    }

    print_error("unsupported sort %s", symbol);
    pstack_error(pstack);
}

/*****************************************
 * Term evaluation
 ****************************************/

/**
 * [ "var-symbol" ]
 */
void pstack_eval_var(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating var term\n");

    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);
    char *symbol = pstack_get_elem_symbol(pstack, 1);

    term_t *new = context_find_var_symbol(ctx, symbol);
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ "true" ]
 */
void pstack_eval_true(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating true term\n");

    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);

    term_t *new = new_bool_sort();
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ "false" ]
 */
void pstack_eval_false(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating false term\n");

    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 1);

    term_t *new = new_bool_sort();
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ "not", <bool-term> ]
 */
void pstack_eval_not(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating not term\n");
    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 2, TAG_TERM);

    term_t *t = pstack_get_elem_term(pstack, 2);
    if (!is_bool_sort(t)) 
        pstack_error(pstack);

    term_t *new = new_bool_sort();
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ "and", <bool-term>, <bool-term> ]
 */
void pstack_eval_and(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating and term\n");

    uint32_t lineno, col;
    lineno = pstack_top_frame(pstack)->lineno;
    col = pstack_top_frame(pstack)->col;

    check_frame_size_eq(pstack, 3);
    check_elem_tag(pstack, 2, TAG_TERM);
    check_elem_tag(pstack, 3, TAG_TERM);

    term_t *lhs, *rhs;
    lhs = pstack_get_elem_term(pstack, 2);
    rhs = pstack_get_elem_term(pstack, 3);
    if (!is_bool_sort(lhs) || !is_bool_sort(rhs)) 
        pstack_error(pstack);

    term_t *new = new_bool_sort();
    pstack_pop_frame(pstack);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ "extract" <numeral> <numeral> <bitvec-term> ]
 * 
 * ((_ extract i j) (_ BitVec m) (_ BitVec n))
 * subject to:
 * - m > i ≥ j ≥ 0
 * - n = i - j + 1
 */
void pstack_eval_bvextract(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating bvextract term\n");
    uint32_t lineno, col;

    lineno = pstack_get_elem_lineno(pstack, 1);
    col = pstack_get_elem_col(pstack, 1);

    check_frame_size_eq(pstack, 4);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_NUMERAL);
    check_elem_tag(pstack, 3, TAG_NUMERAL);
    check_elem_tag(pstack, 4, TAG_TERM);

    uint32_t i, j, m, n;
    term_t *t, *new;

    i = pstack_get_elem_numeral(pstack, 2);
    j = pstack_get_elem_numeral(pstack, 3);
    t = pstack_get_elem_term(pstack, 4);

    if (i < j)
        pstack_error(pstack);
    if (j <= 0) 
        pstack_error(pstack);
    if (!is_bitvec_sort(t))
        pstack_error(pstack);
    m = get_bitvec_width(t);
    if (m <= i) 
        pstack_error(pstack);
    n = i - j + 1;
    new = new_bitvec_sort(n);
    pstack_push_term(pstack, new, lineno, col);
}

/**
 * [ <symbol> <term>* ]
 */
void pstack_eval_term(pstack_t *pstack, context_t *ctx)
{
    fprintf(stderr, "pstack: evaluating term\n");
    check_frame_size_gte(pstack, 1);
    check_elem_tag(pstack, 1, TAG_SYMBOL);

    char *symbol = pstack_get_elem_symbol(pstack, 1);

    if (!strcmp(symbol, "true")) {
        pstack_eval_true(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "false")) {
        pstack_eval_false(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "not")) {
        pstack_eval_not(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "and")) {
        pstack_eval_and(pstack, ctx);
        return;
    } else if (!strcmp(symbol, "extract")) {
        pstack_eval_bvextract(pstack, ctx);
        return;
    } else if (context_find(ctx, symbol) == SYM_KIND_VARIABLE) {
        pstack_eval_var(pstack, ctx);
        return;
    }

    print_error("unsupported term %s", symbol);
    pstack_error(pstack);
}

void pstack_eval_define_system(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_check_system(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_declare_sort(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_declare_enum_sort(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_declare_fun(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_define_sort(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }
void pstack_eval_define_const(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }

/**
 * [<symbol>, <sort>+, <term>]
 */
void pstack_eval_define_fun(pstack_t *pstack, context_t *ctx) 
{
    fprintf(stderr, "pstack: evaluating define-fun\n");

    check_frame_size_gte(pstack, 3);
    uint32_t nargs, i;
    nargs = pstack_top_frame_size(pstack) - 3;

    check_elem_tag(pstack, 1, TAG_SYMBOL);
    for (i = 2; i < nargs + 3; ++i) {
        check_elem_tag(pstack, i, TAG_SORT);
    }
    check_elem_tag(pstack, nargs + 3, TAG_TERM);

    char *symbol;
    sort_t *sort_list, *tmp;

    sort_list = malloc(sizeof(sort_t) * (nargs + 1));
    symbol = pstack_get_elem_symbol(pstack, 1);
    for (i = 2; i < nargs + 3; ++i) {
        tmp = pstack_get_elem_sort(pstack, i);
        // FIXME: we're just copying everything here...
        sort_list[i].symbol = tmp->symbol;
        sort_list[i].num_indices = tmp->num_indices;
        sort_list[i].indices = tmp->indices;
        sort_list[i].num_params = tmp->num_params;
        sort_list[i].params = tmp->params;
    }

    context_add_function_symbol(ctx, symbol, sort_list, nargs + 1);
    context_reset_var_symbols(ctx);
    pstack_pop_frame(pstack);
}

/**
 * [<symbol>, <sort>]
 */
void pstack_eval_var_decl(pstack_t *pstack, context_t *ctx) 
{
    fprintf(stderr, "pstack: evaluating var decl\n");

    check_frame_size_eq(pstack, 2);
    check_elem_tag(pstack, 1, TAG_SYMBOL);
    check_elem_tag(pstack, 2, TAG_SORT);

    uint32_t lineno, col;
    lineno = pstack_get_elem_lineno(pstack, 2);
    col = pstack_get_elem_col(pstack, 2);

    char *symbol = pstack_get_elem_symbol(pstack, 1);
    sort_t *sort = pstack_get_elem_sort(pstack, 2);
    context_add_var_symbol(ctx, symbol, sort);

    pstack_pop_frame(pstack);
    pstack_push_sort(pstack, sort, lineno, col);
}

void pstack_eval_term_binder(pstack_t *pstack, context_t *ctx) { pstack_error(pstack); }

void pstack_noop(pstack_t *pstack, context_t *ctx) 
{
    pstack_pop_frame(pstack);
}

void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, context_t *) = {
    pstack_noop,            // FRM_NOOP,
    pstack_eval_sort,       // FRM_SORT,
    pstack_eval_term,       // FRM_TERM,
    pstack_noop,            // FRM_DEFINE_SYS,
    pstack_noop,            // FRM_CHECK_SYS,
    pstack_noop,            // FRM_DECLARE_SORT,
    pstack_noop,            // FRM_DECLARE_ENUM_SORT,
    pstack_noop,            // FRM_DECLARE_CONST,
    pstack_noop,            // FRM_DECLARE_FUN,
    pstack_noop,            // FRM_DEFINE_SORT,
    pstack_noop,            // FRM_DEFINE_CONST,
    pstack_eval_define_fun, // FRM_DEFINE_FUN,
    pstack_eval_var_decl,   // FRM_VAR_DECL,
    pstack_noop,            // FRM_TERM_BIND,
    pstack_noop             // FRM_ERROR
};

void pstack_eval_frame(pstack_t *pstack, context_t *ctx)
{
    pstack_elem_t *top;
    frame_type_t top_frame_type;

    top = pstack_top_frame(pstack);
    fprintf(stderr, "pstack: evaluating frame idx=%d\n", pstack->frame);
    pstack_print_frame(pstack);
    top_frame_type = top->value.frame_type;
    frame_eval_table[top_frame_type](pstack, ctx);
}

void pstack_print_frame(pstack_t *pstack)
{
    uint32_t i;
    tag_t tag;
    frame_type_t frame_type;

    frame_type = pstack->data[pstack->frame].value.frame_type;
    fprintf(stderr, "%s ", frame_str[frame_type]);

    for (i = pstack->frame + 1; i < pstack->top; ++i) {
        tag = pstack->data[i].tag;
        fprintf(stderr, "%s ", tag_str[tag]);
    }
    fprintf(stderr, "   (|frame| = %d) \n", pstack_top_frame_size(pstack));
}
