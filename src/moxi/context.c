/**
 *
 */
#include <stdio.h>

#include "io/print.h"
#include "moxi/context.h"
#include "moxi/hash_logic.h"

static void default_delete_entry(void *entry) { }

static void delete_var_stack_entry(void *entry) 
{ 
    str_vector_t *vec = (str_vector_t *)entry;
    delete_str_vector(vec);
}

static void delete_symbol_table_entry(void *entry) 
{ 
    symbol_t *symbol = (symbol_t *) entry;
    delete_symbol(symbol);
}

static void delete_system_table_entry(void *entry) 
{ 
    system_t *sys = (symbol_t *) entry;
    free(sys);
}

void activate_core_symbols(moxi_context_t *ctx)
{
    ctx->active_symbols[SYM_BOOL] = true;
    ctx->active_symbols[SYM_TRUE] = true;
    ctx->active_symbols[SYM_FALSE] = true;
    ctx->active_symbols[SYM_NOT] = true;
    ctx->active_symbols[SYM_AND] = true;
    ctx->active_symbols[SYM_OR] = true;
    ctx->active_symbols[SYM_IMPLIES] = true;
    ctx->active_symbols[SYM_XOR] = true;
    ctx->active_symbols[SYM_EQ] = true;
    ctx->active_symbols[SYM_DISTINCT] = true;
    ctx->active_symbols[SYM_ITE] = true;
}

void activate_bitvec_symbols(moxi_context_t *ctx)
{
    ctx->active_symbols[SYM_BITVEC] = true;
    ctx->active_symbols[SYM_CONCAT] = true;
    ctx->active_symbols[SYM_EXTRACT] = true;
    ctx->active_symbols[SYM_REPEAT] = true;
    ctx->active_symbols[SYM_BVCOMP] = true;
    ctx->active_symbols[SYM_BVREDAND] = true;
    ctx->active_symbols[SYM_BVREDOR] = true;
    ctx->active_symbols[SYM_BVNOT] = true;
    ctx->active_symbols[SYM_BVAND] = true;
    ctx->active_symbols[SYM_BVOR] = true;
    ctx->active_symbols[SYM_BVNAND] = true;
    ctx->active_symbols[SYM_BVNOR] = true;
    ctx->active_symbols[SYM_BVXOR] = true;
    ctx->active_symbols[SYM_BVXNOR] = true;
    ctx->active_symbols[SYM_BVNEG] = true;
    ctx->active_symbols[SYM_BVADD] = true;
    ctx->active_symbols[SYM_BVSUB] = true;
    ctx->active_symbols[SYM_BVMUL] = true;
    ctx->active_symbols[SYM_BVUDIV] = true;
    ctx->active_symbols[SYM_BVUREM] = true;
    ctx->active_symbols[SYM_BVSDIV] = true;
    ctx->active_symbols[SYM_BVSREM] = true;
    ctx->active_symbols[SYM_BVSMOD] = true;
    ctx->active_symbols[SYM_BVSHL] = true;
    ctx->active_symbols[SYM_BVLSHR] = true;
    ctx->active_symbols[SYM_BVASHR] = true;
    ctx->active_symbols[SYM_ZERO_EXTEND] = true;
    ctx->active_symbols[SYM_SIGN_EXTEND] = true;
    ctx->active_symbols[SYM_ROTATE_LEFT] = true;
    ctx->active_symbols[SYM_ROTATE_RIGHT] = true;
    ctx->active_symbols[SYM_BVULT] = true;
    ctx->active_symbols[SYM_BVULE] = true;
    ctx->active_symbols[SYM_BVUGT] = true;
    ctx->active_symbols[SYM_BVUGE] = true;
    ctx->active_symbols[SYM_BVSLT] = true;
    ctx->active_symbols[SYM_BVSLE] = true;
    ctx->active_symbols[SYM_BVSGT] = true;
    ctx->active_symbols[SYM_BVSGE] = true;
}

void activate_array_symbols(moxi_context_t *ctx)
{
    ctx->active_symbols[SYM_ARRAY] = true;
    ctx->active_symbols[SYM_SELECT] = true;
    ctx->active_symbols[SYM_STORE] = true;
}

void activate_int_symbols(moxi_context_t *ctx)
{
    ctx->active_symbols[SYM_INT] = true;
    ctx->active_symbols[SYM_PLUS] = true;
    ctx->active_symbols[SYM_MINUS] = true;
    ctx->active_symbols[SYM_TIMES] = true;
    ctx->active_symbols[SYM_DIV] = true;
    ctx->active_symbols[SYM_MOD] = true;
    ctx->active_symbols[SYM_ABS] = true;
    ctx->active_symbols[SYM_GT] = true;
    ctx->active_symbols[SYM_GE] = true;
    ctx->active_symbols[SYM_LT] = true;
    ctx->active_symbols[SYM_LE] = true;
}

void activate_real_symbols(moxi_context_t *ctx)
{
    fprintf(stderr, "activating real symbols\n");
    ctx->active_symbols[SYM_REAL] = true;
    ctx->active_symbols[SYM_PLUS] = true;
    ctx->active_symbols[SYM_MINUS] = true;
    ctx->active_symbols[SYM_TIMES] = true;
    ctx->active_symbols[SYM_DIV] = true;
    ctx->active_symbols[SYM_MOD] = true;
    ctx->active_symbols[SYM_ABS] = true;
    ctx->active_symbols[SYM_GT] = true;
    ctx->active_symbols[SYM_GE] = true;
    ctx->active_symbols[SYM_LT] = true;
    ctx->active_symbols[SYM_LE] = true;
}

void activate_int_real_symbols(moxi_context_t *ctx)
{
    ctx->active_symbols[SYM_TO_REAL] = true;
    ctx->active_symbols[SYM_TO_INT] = true;
}

/**
 * Sets all non-core symbols in `active_symbols` to `false`.
 */
void reset_symbols(moxi_context_t *ctx)
{
    size_t i;
    for (i = 0; i < NUM_SYMBOLS; ++i) {
        ctx->active_symbols[i] = false;
    }
    activate_core_symbols(ctx);
}

void init_context(moxi_context_t *ctx)
{
    init_str_map(&ctx->sort_table, 0, delete_symbol_table_entry);
    init_str_map(&ctx->term_table, 0, delete_symbol_table_entry);
    init_str_map(&ctx->var_table, 0, default_delete_entry);
    init_str_map(&ctx->sys_table, 0, default_delete_entry);
    init_stack(&ctx->scope_stack, delete_var_stack_entry);
    ctx->logic = &no_logic;
    activate_core_symbols(ctx);
}

void delete_context(moxi_context_t *ctx)
{
    delete_str_map(&ctx->sort_table);
    delete_str_map(&ctx->term_table);
    delete_str_map(&ctx->var_table);
    delete_str_map(&ctx->sys_table);
    delete_stack(&ctx->scope_stack);
}


/**
 * Sets the logic in `ctx` to the one defined by `symbol`. Returns true if
 * `symbol` is a valid logic, `false` otherwise.
 */
bool set_current_logic(moxi_context_t *ctx, char *str)
{
    size_t len = strlen(str);
    const logic_t *logic = in_moxi_logic(str, len);
    if (logic == NULL) {
        PRINT_ERROR("unknown logic '%s'", str);
        ctx->logic = &unkown_logic;
        return false;
    }
    logic_type_t type = logic->type;
    ctx->logic = logic;

    if (!logic_is_supported[type]) {
        PRINT_ERROR("unsupported logic '%s'", logic->name);
        return false;
    }

    reset_symbols(ctx);

    if (logic_has_ints[type]) {
        activate_int_symbols(ctx);
    }
    if (logic_has_reals[type]) {
        activate_real_symbols(ctx);
    }
    if (logic_has_ints[type] && logic_has_reals[type]) {
        activate_int_real_symbols(ctx);
    }
    if (logic_has_bitvectors[type]) {
        activate_bitvec_symbols(ctx);
    }
    if (logic_has_arrays[type]) {
        activate_array_symbols(ctx);
    }

    return true;
}


bool moxi_declare_fun(moxi_context_t *ctx, char *str, uint32_t nargs,
                     sort_t *args, sort_t ret)
{
    const symbol_t *theory_symbol = moxi_find_term(ctx, str);
    if (theory_symbol != NULL) {
        return false;
    }

    size_t len = strlen(str);
    symbol_t *symbol = new_symbol(str, len, SYM_UNKNOWN, SYM_KIND_TERM);
    str_map_add(&ctx->term_table, str, len, symbol);

    type_t type;
    if (nargs == 0) {
        type = ret;
    } else {
        type = yices_function_type(nargs, args, ret);
    }
    term_t term = yices_new_uninterpreted_term(type);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        return false;
    }
    yices_set_term_name(term, str);
    return true;
}


bool moxi_define_fun(moxi_context_t *ctx, char *str, uint32_t nargs,
                     sort_t *args, sort_t ret, term_t body)
{
    // Since we are only doing sort checking, we can safely ignore the body of
    // the function definition. The body is checked in `pstack.c`.
    return moxi_declare_fun(ctx, str, nargs, args, ret);
}


const symbol_t *moxi_find_term(moxi_context_t *ctx, char *str)
{
    size_t len = strlen(str);
    const symbol_t *symbol = get_symbol(str, len);
    if (symbol != NULL && ctx->active_symbols[symbol->type] &&
        symbol->kind == SYM_KIND_TERM) {
        return symbol;
    }
    if (str_is_primed(str, len)) {
        char *base_str = strndup(str, len - 1);
        return str_map_find(&ctx->term_table, base_str);
    }
    return str_map_find(&ctx->term_table, str);
}


void moxi_push_scope(moxi_context_t *ctx)
{
    str_vector_t *vec = malloc(sizeof(str_vector_t));
    init_str_vector(vec, 16);
    stack_push(&ctx->scope_stack, vec);
}


void moxi_pop_scope(moxi_context_t *ctx)
{
    str_vector_t *vec = stack_pop(&ctx->scope_stack);
    uint32_t i;
    for (i = 0; i < vec->size; ++i) {
        str_map_remove(&ctx->term_table, vec->data[i]);
        str_map_remove(&ctx->var_table, vec->data[i]);
    }
    delete_str_vector(vec);
    free(vec);
}


bool moxi_add_var(moxi_context_t *ctx, char *str, var_kind_t kind,
                     term_t var)
{
    const symbol_t *theory_symbol = moxi_find_term(ctx, str);
    if (theory_symbol != NULL) {
        return false;
    }

    size_t len = strlen(str);
    symbol_t *symbol = new_symbol(str, len, SYM_VAR, SYM_KIND_VAR);
    str_map_add(&ctx->term_table, str, len, symbol);

    var_table_entry_t *entry = malloc(sizeof(var_table_entry_t));
    entry->kind = kind;
    entry->var = var;
    str_map_add(&ctx->var_table, str, len, entry);

    str_vector_t *vec = stack_top(&ctx->scope_stack);
    str_vector_append(vec, str);

    return true;
}


var_table_entry_t *moxi_find_var(moxi_context_t *ctx, char *str)
{
    size_t len = strlen(str);
    if (str_is_primed(str, len)) {
        char *base_str = strndup(str, len - 1);
        return str_map_find(&ctx->var_table, base_str);
    }
    return str_map_find(&ctx->var_table, str);
}


bool moxi_declare_sort(moxi_context_t *ctx, char *str, uint32_t arity)
{
    const symbol_t *theory_symbol = moxi_find_sort(ctx, str);
    if (theory_symbol != NULL) {
        return false;
    }

    if (arity != 0) {
        return false;
    }

    size_t len = strlen(str);
    symbol_t *symbol = new_symbol(str, len, SYM_UNKNOWN, SYM_KIND_SORT);
    str_map_add(&ctx->sort_table, str, len, symbol);

    sort_t sort = yices_new_uninterpreted_type();
    yices_set_type_name(sort, str);
    return true;
}


const symbol_t *moxi_find_sort(moxi_context_t *ctx, char *str)
{
    size_t len = strlen(str);
    const symbol_t *symbol = get_symbol(str, len);
    if (symbol != NULL && ctx->active_symbols[symbol->type] && symbol->kind == SYM_KIND_SORT) {
        return symbol;
    }
    return str_map_find(&ctx->sort_table, str);
}


bool moxi_define_system(moxi_context_t *ctx, char *str, uint32_t ninput,
                        sort_t *input, uint32_t noutput, sort_t *output,
                        uint32_t nlocal, sort_t *local, term_t init,
                        term_t trans, term_t inv)
{
    system_t *sys = moxi_find_system(ctx, str);
    if (sys != NULL) {
        return false;
    }

    sys = malloc(sizeof(system_t));
    sys->name = malloc((strlen(str) + 1) * sizeof(char));
    strcpy(sys->name, str);

    sys->ninput = ninput;
    sys->input = malloc(ninput * sizeof(sort_t));
    memcpy(sys->input, input, ninput * sizeof(sort_t));

    sys->noutput = noutput;
    sys->output = malloc(noutput * sizeof(sort_t));
    memcpy(sys->output, output, noutput * sizeof(sort_t));

    str_map_add(&ctx->sys_table, str, strlen(str), sys);
    return true;
}


system_t *moxi_find_system(moxi_context_t *ctx, char *str)
{
    return str_map_find(&ctx->sys_table, str);
}