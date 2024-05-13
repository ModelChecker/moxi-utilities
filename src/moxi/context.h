/**
 * 
*/
#ifndef __CONTEXT_H__
#define __CONTEXT_H__

#include <stdbool.h>

#include "util/string_pair_list.h"
#include "util/symbol_table.h"

#include "moxi/logics.h"
#include "moxi/sort_table.h"
#include "moxi/sorts.h"
#include "moxi/terms.h"
#include "moxi/systems.h"


typedef enum symbol_kind {
    MOXI_SYM_KIND_SORT,
    MOXI_SYM_KIND_FUNCTION,
    MOXI_SYM_KIND_VARIABLE,
    MOXI_SYM_KIND_SYSTEM,
    MOXI_SYM_KIND_NONE
} symbol_kind_t;


/**
 * Stores information on symbols and their interpretations including
 * - sorts
 * - functions (possibly uninterpreted)
 * - variables
 * - systems
 * 
 * Note: we don't allow shadowing of sort/function/system symbols.
*/
typedef struct context {

    logic_t current_logic;

    /**
     * Maps symbols to their kind. Use this to track all symbols currently in use and which table to
     * perform an actual lookup (e.g., `sort_table`, `function_table`, etc.).
     * 
     * "sort-symbol" ->   `MOXI_SYM_KIND_SORT`
     * "fun-symbol" ->    `MOXI_SYM_KIND_FUNCTION`
     * "var-symbol" ->    `MOXI_SYM_KIND_VARIABLE`
     * "system-symbol" -> `MOXI_SYM_KIND_SYSTEM`
    */  
    symbol_table_t symbol_table;

    /**
     * Maps sort symbols to their arity.
     * 
     * "sort-id" -> arity
    */
    sort_table_t sort_table;

    /**
     * Maps function symbols to their rank and term, if available. A rank is a list of sort/variable
     * symbol pairs. Its term is unavailable (NULL) if it is an uninterpreted function.
     *
     * "fun-id" -> ([("var1", "sort1"), ..., ("varN", "sortN")], term)
    */
    symbol_table_t function_table;

    /**
     * Maps system symbols to their definitions.
     *
     * "sys-id" -> <system-definition>
    */
    symbol_table_t system_table;

    /**
     * Maps variables to their sorts.
     *
     * "var-id" -> sort symbol
    */
    symbol_table_t variable_table;

} context_t;


void init_context(context_t *context);
void delete_context(context_t *context);

symbol_kind_t context_find(context_t *context, char *symbol);

bool context_add_function_symbol(context_t *context, char *symbol, string_pair_list_t *rank, term_t *term);
bool context_remove_function_symbol(context_t *context, char *symbol);
bool context_add_sort_symbol(context_t *context, char *symbol);
bool context_add_system_symbol(context_t *context, char *symbol);


#endif