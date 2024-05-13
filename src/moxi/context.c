/**
 * 
*/
#include "context.h"


void init_context(context_t *context)
{
    symbol_table_t *symbol_table = &context->symbol_table;
    sort_table_t *sort_table = &context->sort_table;

    init_symbol_table(symbol_table, 0);
    init_sort_table(sort_table, 0);

    symbol_table_add(symbol_table, "Bool", MOXI_SYM_KIND_SORT);
    sort_table_add(sort_table, "Bool", 0);

    symbol_table_add(symbol_table, "true", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "false", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "not", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "and", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "or", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "=>", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "xor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "=", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "distinct", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "ite", MOXI_SYM_KIND_FUNCTION);

}


// void delete_context(context_t *context);

// symbol_kind_t context_find(context_t *context, char *symbol);

// bool context_add_function_symbol(context_t *context, char *symbol, string_pair_list_t *rank, term_t *term);
// bool context_remove_function_symbol(context_t *context, char *symbol);
// bool context_add_sort_symbol(context_t *context, char *symbol);
// bool context_add_system_symbol(context_t *context, char *symbol);
