/**
 *
 */
#include <string.h>
#include <stdio.h>

#include "io/print.h"
#include "moxi/context.h"
#include "moxi/hash_logic.h"
#include "parse/hash_symbol.h"

void activate_core_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_BOOL] = true;
    ctx->active_theory_symbols[THY_SYM_TRUE] = true;
    ctx->active_theory_symbols[THY_SYM_FALSE] = true;
    ctx->active_theory_symbols[THY_SYM_NOT] = true;
    ctx->active_theory_symbols[THY_SYM_AND] = true;
    ctx->active_theory_symbols[THY_SYM_OR] = true;
    ctx->active_theory_symbols[THY_SYM_IMPLIES] = true;
    ctx->active_theory_symbols[THY_SYM_XOR] = true;
    ctx->active_theory_symbols[THY_SYM_EQ] = true;
    ctx->active_theory_symbols[THY_SYM_DISTINCT] = true;
    ctx->active_theory_symbols[THY_SYM_ITE] = true;
}

void activate_bitvec_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_BITVEC] = true;
    ctx->active_theory_symbols[THY_SYM_CONCAT] = true;
    ctx->active_theory_symbols[THY_SYM_EXTRACT] = true;
    ctx->active_theory_symbols[THY_SYM_REPEAT] = true;
    ctx->active_theory_symbols[THY_SYM_BVCOMP] = true;
    ctx->active_theory_symbols[THY_SYM_BVREDAND] = true;
    ctx->active_theory_symbols[THY_SYM_BVREDOR] = true;
    ctx->active_theory_symbols[THY_SYM_BVNOT] = true;
    ctx->active_theory_symbols[THY_SYM_BVAND] = true;
    ctx->active_theory_symbols[THY_SYM_BVOR] = true;
    ctx->active_theory_symbols[THY_SYM_BVNAND] = true;
    ctx->active_theory_symbols[THY_SYM_BVNOR] = true;
    ctx->active_theory_symbols[THY_SYM_BVXOR] = true;
    ctx->active_theory_symbols[THY_SYM_BVXNOR] = true;
    ctx->active_theory_symbols[THY_SYM_BVNEG] = true;
    ctx->active_theory_symbols[THY_SYM_BVADD] = true;
    ctx->active_theory_symbols[THY_SYM_BVSUB] = true;
    ctx->active_theory_symbols[THY_SYM_BVMUL] = true;
    ctx->active_theory_symbols[THY_SYM_BVUDIV] = true;
    ctx->active_theory_symbols[THY_SYM_BVUREM] = true;
    ctx->active_theory_symbols[THY_SYM_BVSDIV] = true;
    ctx->active_theory_symbols[THY_SYM_BVSREM] = true;
    ctx->active_theory_symbols[THY_SYM_BVSMOD] = true;
    ctx->active_theory_symbols[THY_SYM_BVSHL] = true;
    ctx->active_theory_symbols[THY_SYM_BVLSHR] = true;
    ctx->active_theory_symbols[THY_SYM_BVASHR] = true;
    ctx->active_theory_symbols[THY_SYM_ZERO_EXTEND] = true;
    ctx->active_theory_symbols[THY_SYM_SIGN_EXTEND] = true;
    ctx->active_theory_symbols[THY_SYM_ROTATE_LEFT] = true;
    ctx->active_theory_symbols[THY_SYM_ROTATE_RIGHT] = true;
    ctx->active_theory_symbols[THY_SYM_BVULT] = true;
    ctx->active_theory_symbols[THY_SYM_BVULE] = true;
    ctx->active_theory_symbols[THY_SYM_BVUGT] = true;
    ctx->active_theory_symbols[THY_SYM_BVUGE] = true;
    ctx->active_theory_symbols[THY_SYM_BVSLT] = true;
    ctx->active_theory_symbols[THY_SYM_BVSLE] = true;
    ctx->active_theory_symbols[THY_SYM_BVSGT] = true;
    ctx->active_theory_symbols[THY_SYM_BVSGE] = true;
}

void activate_array_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_ARRAY] = true;
    ctx->active_theory_symbols[THY_SYM_SELECT] = true;
    ctx->active_theory_symbols[THY_SYM_STORE] = true;
}

void activate_int_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_INT] = true;
    ctx->active_theory_symbols[THY_SYM_PLUS] = true;
    ctx->active_theory_symbols[THY_SYM_MINUS] = true;
    ctx->active_theory_symbols[THY_SYM_TIMES] = true;
    ctx->active_theory_symbols[THY_SYM_DIVISIBLE] = true;
    ctx->active_theory_symbols[THY_SYM_MOD] = true;
    ctx->active_theory_symbols[THY_SYM_ABS] = true;
    ctx->active_theory_symbols[THY_SYM_GT] = true;
    ctx->active_theory_symbols[THY_SYM_GE] = true;
    ctx->active_theory_symbols[THY_SYM_LT] = true;
    ctx->active_theory_symbols[THY_SYM_LE] = true;
}

void activate_real_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_REAL] = true;
    ctx->active_theory_symbols[THY_SYM_PLUS] = true;
    ctx->active_theory_symbols[THY_SYM_MINUS] = true;
    ctx->active_theory_symbols[THY_SYM_TIMES] = true;
    ctx->active_theory_symbols[THY_SYM_DIVISIBLE] = true;
    ctx->active_theory_symbols[THY_SYM_MOD] = true;
    ctx->active_theory_symbols[THY_SYM_ABS] = true;
    ctx->active_theory_symbols[THY_SYM_GT] = true;
    ctx->active_theory_symbols[THY_SYM_GE] = true;
    ctx->active_theory_symbols[THY_SYM_LT] = true;
    ctx->active_theory_symbols[THY_SYM_LE] = true;
}

void activate_int_real_symbols(moxi_context_t *ctx)
{
    ctx->active_theory_symbols[THY_SYM_TO_REAL] = true;
    ctx->active_theory_symbols[THY_SYM_TO_INT] = true;
}

static void default_delete_entry(void *entry) { }

static void delete_var_stack_entry(void *entry) 
{ 
    str_vector_t *vec = (str_vector_t *)entry;
    delete_str_vector(vec);
}

static void delete_sys_table_entry(void *entry) 
{ 
    sys_table_entry_t *sys = (sys_table_entry_t *) entry;
    free(sys->name);
    free(sys->input);
    free(sys->output);
    free(sys);
}

/**
 * Sets all non-core symbols in `active_symbols` to `false`.
 */
void reset_symbols(moxi_context_t *ctx)
{
    size_t i;
    for (i = 0; i < NUM_THEORY_SYMBOLS; ++i) {
        ctx->active_theory_symbols[i] = false;
    }
    activate_core_symbols(ctx);
}

void init_context(moxi_context_t *ctx)
{
    ctx->status = 0;
    init_str_map(&ctx->var_table, 0, default_delete_entry);
    init_str_map(&ctx->sys_table, 0, delete_sys_table_entry);
    init_stack(&ctx->scope_stack, delete_var_stack_entry);
    ctx->logic = &no_logic;
    activate_core_symbols(ctx);
}

void delete_context(moxi_context_t *ctx)
{
    delete_str_map(&ctx->var_table);
    delete_str_map(&ctx->sys_table);
    delete_stack(&ctx->scope_stack);
}

theory_symbol_type_t get_theory_symbol_type(const moxi_context_t *ctx, const char *symbol)
{
    const theory_symbol_t *thy_sym = find_moxi_thy_sym(symbol, strlen(symbol));
    if (thy_sym != NULL) {
        return thy_sym->type;
    }
    return THY_SYM_UNKNOWN;
}

bool is_active_theory_term(const moxi_context_t *ctx, const char *symbol)
{
    const theory_symbol_t *thy_sym = find_moxi_thy_sym(symbol, strlen(symbol));
    return (thy_sym != NULL && thy_sym->kind == TERM && ctx->active_theory_symbols[thy_sym->type]);
}

bool is_active_theory_sort(const moxi_context_t *ctx, const char *symbol)
{
    const theory_symbol_t *thy_sym = find_moxi_thy_sym(symbol, strlen(symbol));
    return (thy_sym != NULL && thy_sym->kind == SORT && ctx->active_theory_symbols[thy_sym->type]);
}

bool is_active_term(const moxi_context_t *ctx, const char *symbol)
{
    return is_active_theory_term(ctx, symbol) || (yices_get_term_by_name(symbol) != NULL_TERM);
}

bool is_active_sort(const moxi_context_t *ctx, const char *symbol)
{
    return is_active_theory_sort(ctx, symbol) || (yices_get_type_by_name(symbol) != NULL_TYPE);
}

/**
 * Sets the logic in `ctx` to the one defined by `symbol`. Returns true if
 * `symbol` is a valid logic, `false` otherwise.
 */
void moxi_set_logic(moxi_context_t *ctx, char *symbol)
{
    size_t len = strlen(symbol);
    const logic_t *logic = find_moxi_logic(symbol, len);
    if (logic == NULL) {
        PRINT_ERROR("unknown logic '%s'", symbol);
        ctx->logic = &unkown_logic;
        ctx->status = 1;
        return;
    }
    logic_type_t type = logic->type;
    ctx->logic = logic;

    if (!logic_is_supported[type]) {
        PRINT_ERROR("unsupported logic '%s'", logic->name);
        ctx->status = 1;
        return;
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
}


void moxi_declare_fun(moxi_context_t *ctx, char *symbol, size_t nargs,
                     sort_t *args, sort_t ret)
{
    if (is_active_term(ctx, symbol)) {
        ctx->status = 1;
        return;
    }

    type_t type;
    if (nargs == 0) {
        type = ret;
    } else {
        type = yices_function_type(nargs, args, ret);
    }
    term_t term = yices_new_uninterpreted_term(type);
    if (term == NULL_TERM) {
        yices_print_error(stderr);
        ctx->status = 1;
        return;
    }
    yices_set_term_name(term, symbol);
}


void moxi_define_fun(moxi_context_t *ctx, char *str, size_t nargs,
                     sort_t *args, sort_t ret, term_t body)
{
    // Since we are only doing sort checking, we can safely ignore the body of
    // the function definition. The body is checked in `pstack.c`.
    moxi_declare_fun(ctx, str, nargs, args, ret);
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
    size_t i;
    for (i = 0; i < vec->size; ++i) {
        str_map_remove(&ctx->var_table, vec->data[i]);
        yices_remove_term_name(vec->data[i]);
        fprintf(stderr, "removing %s\n", vec->data[i]);
    }
    delete_str_vector(vec);
    free(vec);
}


str_vector_t *moxi_get_scope(moxi_context_t *ctx)
{
    return stack_top(&ctx->scope_stack);
}


/**
 * Adds `symbol` to the term table, variable table, and the current scope.
 */
void moxi_add_var(moxi_context_t *ctx, char *symbol, term_t var, var_kind_t kind)
{
    if (is_active_term(ctx, symbol)) {
        ctx->status = 1;
        return;
    }

    var_table_entry_t *new_var_entry = malloc(sizeof(var_table_entry_t));
    new_var_entry->kind = kind;
    new_var_entry->var = var;
    new_var_entry->is_primed = false;
    str_map_add(&ctx->var_table, symbol, strlen(symbol), new_var_entry);

    str_vector_t *scope = stack_top(&ctx->scope_stack);
    str_vector_append(scope, symbol);

    yices_set_term_name(var, symbol);

    if (kind == LOGIC_VAR) {
        return;
    }

    // All other var types get a primed version as well
    char *primed = malloc((strlen(symbol) + 2) * sizeof(char));
    sprintf(primed, "%s'", symbol);

    var_table_entry_t *primed_var_entry = malloc(sizeof(var_table_entry_t));
    primed_var_entry->kind = kind;
    primed_var_entry->var = var;
    primed_var_entry->is_primed = true;
    str_map_add(&ctx->var_table, primed, strlen(primed), primed_var_entry);

    str_vector_append(scope, primed);
    yices_set_term_name(var, primed);
}


const var_table_entry_t *moxi_find_var(moxi_context_t *ctx, char *symbol)
{
    return str_map_find(&ctx->var_table, symbol);
}


void moxi_declare_sort(moxi_context_t *ctx, char *symbol, size_t arity)
{
    if (is_active_sort(ctx, symbol)) {
        ctx->status = 1;
        return;
    }
    if (arity != 0) {
        ctx->status = 1;
        return;
    }
    sort_t sort = yices_new_uninterpreted_type();
    yices_set_type_name(sort, symbol);
}


void moxi_define_system(moxi_context_t *ctx, char *str, size_t ninput,
                        sort_t *input, size_t noutput, sort_t *output,
                        size_t nlocal, sort_t *local, term_t init,
                        term_t trans, term_t inv)
{
    const sys_table_entry_t *sys = moxi_find_system(ctx, str);
    if (sys != NULL) {
        ctx->status = 1;
        return;
    }

    sys_table_entry_t *new = malloc(sizeof(sys_table_entry_t));
    new->name = malloc((strlen(str) + 1) * sizeof(char));
    strcpy(new->name, str);

    new->ninput = ninput;
    new->input = malloc(ninput * sizeof(sort_t));
    memcpy(new->input, input, ninput * sizeof(sort_t));

    new->noutput = noutput;
    new->output = malloc(noutput * sizeof(sort_t));
    memcpy(new->output, output, noutput * sizeof(sort_t));

    str_map_add(&ctx->sys_table, str, strlen(str), new);
}


const sys_table_entry_t *moxi_find_system(moxi_context_t *ctx, char *str)
{
    return str_map_find(&ctx->sys_table, str);
}
