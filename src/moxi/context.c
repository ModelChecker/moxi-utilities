/**
 *
 */
#include "context.h"

void init_context(moxi_context_t *context) {
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

// bool context_add_function_symbol(context_t *context, char *symbol,
// string_pair_list_t *rank, term_t *term); bool
// context_remove_function_symbol(context_t *context, char *symbol); bool
// context_add_sort_symbol(context_t *context, char *symbol); bool
// context_add_system_symbol(context_t *context, char *symbol);

void add_bitvec_symbols(moxi_context_t *context) {
    symbol_table_t *symbol_table = &context->symbol_table;
    sort_table_t *sort_table = &context->sort_table;

    symbol_table_add(symbol_table, "BitVec", MOXI_SYM_KIND_SORT);
    sort_table_add(sort_table, "BitVec", 0);

    symbol_table_add(symbol_table, "concat", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "extract", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "repeat", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvcomp", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvredand", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvredor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvnot", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvand", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvnand", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvnor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvxor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvxnor", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvneg", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvadd", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsub", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvmul", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvudiv", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvurem", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsdiv", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsrem", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsmod", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvshl", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvlshr", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvashr", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "zero_extend", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "sign_extend", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "rotate_left", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "rotate_right", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvult", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvule", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvugt", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvuge", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvslt", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsle", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsgt", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "bvsge", MOXI_SYM_KIND_FUNCTION);
}

void add_array_symbols(moxi_context_t *context) {
    symbol_table_t *symbol_table = &context->symbol_table;
    sort_table_t *sort_table = &context->sort_table;

    symbol_table_add(symbol_table, "Array", MOXI_SYM_KIND_SORT);
    sort_table_add(sort_table, "Array", 2);

    symbol_table_add(symbol_table, "select", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "store", MOXI_SYM_KIND_FUNCTION);
}

void add_int_symbols(moxi_context_t *context) {
    symbol_table_t *symbol_table = &context->symbol_table;
    sort_table_t *sort_table = &context->sort_table;

    symbol_table_add(symbol_table, "Int", MOXI_SYM_KIND_SORT);
    sort_table_add(sort_table, "Int", 0);

    symbol_table_add(symbol_table, "+", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "-", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "*", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "div", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "mod", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "abs", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, ">=", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, ">", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "<=", MOXI_SYM_KIND_FUNCTION);
    symbol_table_add(symbol_table, "<", MOXI_SYM_KIND_FUNCTION);
}

void set_current_logic(moxi_context_t *context, logic_t logic) {
    switch (logic) {
    case LOGIC_AX:
        add_array_symbols(context);
        break;
    case LOGIC_BV:
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
