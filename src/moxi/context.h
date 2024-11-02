/**
 *
 */
#ifndef __CONTEXT_H__
#define __CONTEXT_H__

#include <stdbool.h>

#include "moxi/logic.h"
#include "moxi/sort.h"
#include "parse/token.h"
#include "util/str_int_map.h"
#include "util/str_map.h"

typedef enum {
    INPUT_VAR,
    OUTPUT_VAR,
    LOCAL_VAR,
    LOGIC_VAR // Let-bound, quantified, and define-fun variables (can not be primed)
} var_kind_t;

// Stores a variable's kind and sort
typedef struct var_table_entry {
    var_kind_t kind;
    sort_t sort;
} var_table_entry_t;

/**
 * Stores information on symbols and their interpretations.
 */
typedef struct context {
    const logic_t *logic;
    bool active_symbols[NUM_SYMBOLS];

    // Maps symbols to their kind. Use this to track all symbols currently in
    // use and which table to perform an actual lookup (e.g., `sort_table`,
    // `function_table`, etc.).
    str_int_map_t symbol_table;

    // ...
    int_map_t sort_table;

    // Maps variable symbols to their kind (input, output, local) and sort.
    str_map_t var_table;

    // Maps function symbols to their signature and definition. If a function is
    // uninterpreted (i.e., has no definition), then its definition is NULL.
    str_map_t fun_table;

    // Maps systems to their signature.
    str_map_t sys_table;

} context_t;

void init_context(context_t *ctx);
void delete_context(context_t *ctx);

// Returns kind of symbol for `name`. Uses symbol table for user-defined
// symbols.
symbol_kind_t context_find(context_t *ctx, char *name);

// Add `symbol` to the context as a function with rank defined by `rank` and
// `len`. The last element of `rank` is the return sort.
bool context_add_fun_symbol(context_t *ctx, char *symbol, rank_t *rank);
bool context_add_const_symbol(context_t *ctx, char *symbol, sort_t sort);

bool context_remove_symbol(context_t *ctx, char *symbol);
bool context_add_sort_symbol(context_t *ctx, char *symbol);
bool context_add_system_symbol(context_t *ctx, char *symbol);

/**
 * Adds `symbol |-> (kind, sort)` to the context and fails if `symbol` is
 * already in the context. Returns true on success and false on failure.
 */
bool context_add_var_symbol(context_t *ctx, char *symbol, var_kind_t kind,
                            sort_t sort);
var_table_entry_t *context_find_var_symbol(context_t *ctx, char *symbol);

// Removes all local variable symbols from the context.
void context_reset_var_symbols(context_t *ctx);

bool set_current_logic(context_t *ctx, char *symbol, size_t n);

bool is_bool_sort(context_t *ctx, sort_t term);
bool is_int_sort(context_t *ctx, sort_t term);
bool is_real_sort(context_t *ctx, sort_t term);
bool is_bitvec_sort(context_t *ctx, sort_t term);
// bool is_array_sort(context_t *ctx, sort_t term);

#endif