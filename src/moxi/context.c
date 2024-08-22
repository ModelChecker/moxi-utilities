/**
 *
 */
#include "moxi/context.h"

void init_context(context_t *context) 
{
    init_string_int_map(&context->symbol_table, 0);
    init_string_map(&context->var_table, 0);
}

void delete_context(context_t *context)
{
    delete_string_int_map(&context->symbol_table);
    delete_string_map(&context->var_table);
}

symbol_kind_t context_find(context_t *context, char *symbol)
{
    int ret = string_int_map_find(&context->symbol_table, symbol);
    return ret < 0 ? SYM_KIND_NONE : ret;
}

bool context_add_function_symbol(context_t *context, char *symbol,
                                 sort_t *rank, uint32_t rank_size)
{
    return true;
}

// bool context_remove_function_symbol(context_t *context, char *symbol);
// bool context_add_sort_symbol(context_t *context, char *symbol);
// bool context_add_system_symbol(context_t *context, char *symbol);

bool context_add_var_symbol(context_t *context, char *symbol, sort_t *sort)
{
    string_int_map_t *symbol_table;
    string_map_t *var_table;

    symbol_table = &context->symbol_table;
    if (string_int_map_find(symbol_table, symbol) >= 0) {
        return false;
    }
    
    var_table = &context->var_table;
    string_int_map_add(symbol_table, symbol, SYM_KIND_VARIABLE);
    string_map_add(var_table, symbol, (void*) sort);
    return true;
}

sort_t *context_find_var_symbol(context_t *context, char *symbol)
{
    return string_map_find(&context->var_table, symbol);
}

void context_reset_var_symbols(context_t *context)
{

}

void add_core_symbols(context_t *context)
{
    string_int_map_t *symbol_table = &context->symbol_table;

    string_int_map_add(symbol_table, "Bool", SYM_KIND_SORT);

    string_int_map_add(symbol_table, "true", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "false", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "not", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "and", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "or", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "=>", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "xor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "=", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "distinct", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "ite", SYM_KIND_TERM);
}

void add_bitvec_symbols(context_t *context)
{
    string_int_map_t *symbol_table = &context->symbol_table;

    string_int_map_add(symbol_table, "BitVec", SYM_KIND_SORT);

    string_int_map_add(symbol_table, "concat", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "extract", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "repeat", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvcomp", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvredand", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvredor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvnot", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvand", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvnand", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvnor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvxor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvxnor", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvneg", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvadd", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsub", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvmul", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvudiv", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvurem", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsdiv", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsrem", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsmod", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvshl", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvlshr", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvashr", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "zero_extend", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "sign_extend", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "rotate_left", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "rotate_right", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvult", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvule", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvugt", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvuge", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvslt", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsle", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsgt", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "bvsge", SYM_KIND_TERM);
}

void add_array_symbols(context_t *context)
{
    string_int_map_t *symbol_table = &context->symbol_table;

    string_int_map_add(symbol_table, "Array", SYM_KIND_SORT);

    string_int_map_add(symbol_table, "select", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "store", SYM_KIND_TERM);
}

void add_int_symbols(context_t *context)
{
    string_int_map_t *symbol_table = &context->symbol_table;

    string_int_map_add(symbol_table, "Int", SYM_KIND_SORT);

    string_int_map_add(symbol_table, "+", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "-", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "*", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "div", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "mod", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "abs", SYM_KIND_TERM);
    string_int_map_add(symbol_table, ">=", SYM_KIND_TERM);
    string_int_map_add(symbol_table, ">", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "<=", SYM_KIND_TERM);
    string_int_map_add(symbol_table, "<", SYM_KIND_TERM);
}

void set_current_logic(context_t *context, logic_t logic)
{
    switch (logic) {
    case LOGIC_AX:
        add_array_symbols(context);
        break;
    case LOGIC_BV:
        add_bitvec_symbols(context);
        break;
    case LOGIC_IDL:
    case LOGIC_LIA:
    case LOGIC_LRA:
    case LOGIC_LIRA:
    case LOGIC_NIA:
    case LOGIC_NRA:
    case LOGIC_NIRA:
    case LOGIC_RDL:
    case LOGIC_UF:
    case LOGIC_ABV:
    case LOGIC_ALIA:
    case LOGIC_ALRA:
    case LOGIC_ALIRA:
    case LOGIC_ANIA:
    case LOGIC_ANRA:
    case LOGIC_ANIRA:
    case LOGIC_AUF:
    case LOGIC_UFBV:
    case LOGIC_UFBVLIA:
    case LOGIC_UFIDL:
    case LOGIC_UFLIA:
    case LOGIC_UFLRA:
    case LOGIC_UFLIRA:
    case LOGIC_UFNIA:
    case LOGIC_UFNRA:
    case LOGIC_UFNIRA:
    case LOGIC_UFRDL:
    case LOGIC_AUFBV:
    case LOGIC_AUFBVLIA:
    case LOGIC_AUFBVNIA:
    case LOGIC_AUFLIA:
    case LOGIC_AUFLRA:
    case LOGIC_AUFLIRA:
    case LOGIC_AUFNIA:
    case LOGIC_AUFNRA:
    case LOGIC_AUFNIRA:
    case LOGIC_QF_AX:
    case LOGIC_QF_BV:
    case LOGIC_QF_IDL:
    case LOGIC_QF_LIA:
    case LOGIC_QF_LRA:
    case LOGIC_QF_LIRA:
    case LOGIC_QF_NIA:
    case LOGIC_QF_NRA:
    case LOGIC_QF_NIRA:
    case LOGIC_QF_RDL:
    case LOGIC_QF_UF:
    case LOGIC_QF_ABV:
    case LOGIC_QF_ALIA:
    case LOGIC_QF_ALRA:
    case LOGIC_QF_ALIRA:
    case LOGIC_QF_ANIA:
    case LOGIC_QF_ANRA:
    case LOGIC_QF_ANIRA:
    case LOGIC_QF_AUF:
    case LOGIC_QF_UFBV:
    case LOGIC_QF_UFBVLIA:
    case LOGIC_QF_UFIDL:
    case LOGIC_QF_UFLIA:
    case LOGIC_QF_UFLRA:
    case LOGIC_QF_UFLIRA:
    case LOGIC_QF_UFNIA:
    case LOGIC_QF_UFNRA:
    case LOGIC_QF_UFNIRA:
    case LOGIC_QF_UFRDL:
    case LOGIC_QF_AUFBV:
    case LOGIC_QF_AUFBVLIA:
    case LOGIC_QF_AUFBVNIA:
    case LOGIC_QF_AUFLIA:
    case LOGIC_QF_AUFLRA:
    case LOGIC_QF_AUFLIRA:
    case LOGIC_QF_AUFNIA:
    case LOGIC_QF_AUFNRA:
    case LOGIC_QF_AUFNIRA:
    case LOGIC_NONE:
    case LOGIC_ALL:
    case LOGIC_UNKNOWN:
    default:
        break;
    }

    /*
     * Base logics (with quantifiers)
     */
}


