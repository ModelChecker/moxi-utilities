/**
 *
 */
#include <stdio.h>

#include "io/print.h"
#include "moxi/context.h"
#include "moxi/hash_logic.h"

void activate_core_symbols(context_t *ctx)
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

void activate_bitvec_symbols(context_t *ctx)
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

void activate_array_symbols(context_t *ctx)
{
    ctx->active_symbols[SYM_ARRAY] = true;
    ctx->active_symbols[SYM_SELECT] = true;
    ctx->active_symbols[SYM_STORE] = true;
}

void activate_int_symbols(context_t *ctx)
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

void activate_real_symbols(context_t *ctx)
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

void activate_int_real_symbols(context_t *ctx)
{
    activate_int_symbols(ctx);
    activate_real_symbols(ctx);
    ctx->active_symbols[SYM_TO_REAL] = true;
    ctx->active_symbols[SYM_TO_INT] = true;
}

/**
 * Sets all non-core symbols in `active_symbols` to `false`.
 */
void reset_symbols(context_t *ctx)
{
    size_t i;
    for (i = 0; i < NUM_SYMBOLS; ++i) {
        ctx->active_symbols[i] = false;
    }
    activate_core_symbols(ctx);
}

void init_context(context_t *ctx)
{
    init_str_int_map(&ctx->symbol_table, 0);
    init_str_map(&ctx->var_table, 0);
    init_str_map(&ctx->fun_table, 0);
    init_sort_table(&ctx->sort_table);

    ctx->logic = &no_logic;
    activate_core_symbols(ctx);
}

void delete_context(context_t *ctx)
{
    delete_str_int_map(&ctx->symbol_table);
    delete_str_map(&ctx->var_table);
    delete_sort_table(&ctx->sort_table);
}

symbol_kind_t context_find(context_t *ctx, char *name)
{
    const symbol_t *symbol = get_symbol(name);
    if (symbol != NULL && ctx->active_symbols[symbol->type]) {
        return symbol_kind[symbol->type];
    }
    int ret = str_int_map_find(&ctx->symbol_table, name);
    return ret < 0 ? SYM_KIND_NONE : ret;
}

bool context_add_fun_symbol(context_t *ctx, char *symbol, rank_t *rank)
{
    str_int_map_t *symbol_table;
    str_map_t *fun_table;

    symbol_table = &ctx->symbol_table;
    if (str_int_map_find(symbol_table, symbol) >= 0) {
        return false;
    }

    fun_table = &ctx->fun_table;
    str_int_map_add(symbol_table, symbol, strlen(symbol), SYM_KIND_TERM);
    str_map_add(fun_table, symbol, strlen(symbol), (void *)rank);
    // int i = str_int_map_find(symbol_table, symbol);
    // fprintf(stderr, "%d\n", i);
    return true;
}

bool context_add_const_symbol(context_t *ctx, char *symbol, sort_t sort)
{
    sort_t *sort_list = malloc(sizeof(sort_t));
    sort_list[0] = sort;

    rank_t *rank = malloc(sizeof(rank_t));
    rank->sorts = sort_list;
    rank->len = 1;

    return context_add_fun_symbol(ctx, symbol, rank);
}

// bool context_add_sort_symbol(context_t *ctx, char *symbol);
// bool context_add_system_symbol(context_t *ctx, char *symbol);

bool context_add_var_symbol(context_t *ctx, char *symbol, var_kind_t kind,
                            sort_t sort)
{
    str_int_map_t *symbol_table;
    str_map_t *var_table;

    symbol_table = &ctx->symbol_table;
    if (str_int_map_find(symbol_table, symbol) >= 0) {
        return false;
    }
    str_int_map_add(symbol_table, symbol, strlen(symbol), SYM_KIND_VARIABLE);

    var_table = &ctx->var_table;
    var_table_entry_t *entry = malloc(sizeof(var_table_entry_t));
    entry->kind = kind;
    entry->sort = sort;
    str_map_add(var_table, symbol, strlen(symbol), entry);
    return true;
}

bool context_remove_symbol(context_t *ctx, char *symbol)
{
    return false;
}

var_table_entry_t *context_find_var_symbol(context_t *ctx, char *symbol)
{
    return str_map_find(&ctx->var_table, symbol);
}

void context_reset_var_symbols(context_t *ctx) {}

/**
 * Sets the logic in `ctx` to the one defined by `symbol`. Returns true if
 * `symbol` is a valid logic, `false` otherwise.
 */
bool set_current_logic(context_t *ctx, char *symbol, size_t n)
{
    const logic_t *logic = in_moxi_logic(symbol, n);
    if (logic == NULL) {
        PRINT_ERROR("unknown logic '%s'", symbol);
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
    if (logic_has_bitvectors[type]) {
        activate_bitvec_symbols(ctx);
    }
    if (logic_has_arrays[type]) {
        activate_array_symbols(ctx);
    }

    return true;
}

bool is_bool_sort(context_t *ctx, sort_t term)
{
    return term == bool_sort;
}

bool is_int_sort(context_t *ctx, sort_t term)
{
    return term == int_sort;
}

bool is_real_sort(context_t *ctx, sort_t term)
{
    return term == real_sort;
}

bool is_bitvec_sort(context_t *ctx, sort_t term)
{
    sort_obj_t *sort_obj = int_map_find(&ctx->sort_table, term);
    if (sort_obj == NULL) {
        return false;
    }
    return sort_obj->base == bitvec_sort;
}

// bool is_bitvec_sort(context_t *ctx, sort_t term)
// {
//     sort_obj_t *sort_obj = int_map_find(&ctx->sort_table, term);
//     if (sort_obj == NULL) {
//         return false;
//     }
//     return sort_obj->base == bitvec_sort;
// }

// bool is_array_sort(context_t *ctx, sort_t term)
// {
//     sort_obj_t *sort_obj = int_map_find(sort_table, sort);
//     if (sort_obj == NULL) {
//         return false;
//     }
//     return sort_obj->base == array_sort;
// }
