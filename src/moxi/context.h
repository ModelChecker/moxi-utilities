/**
 *
 */
#ifndef __CONTEXT_H__
#define __CONTEXT_H__

#include <stdbool.h>

#include "util/string_list.h"
#include "util/string_int_map.h"
#include "util/string_map.h"
#include "parse/token.h"
#include "moxi/sort.h"

typedef enum logic {
    /*
     * Base logics (with quantifiers)
     */
    LOGIC_AX,   // arrays
    LOGIC_BV,   // bitvectors
    LOGIC_IDL,  // integer difference logic
    LOGIC_LIA,  // linear integer arithmetic
    LOGIC_LRA,  // linear real arithmetic
    LOGIC_LIRA, // mixed linear arithmetic
    LOGIC_NIA,  // non-linear integer arithmetic
    LOGIC_NRA,  // non-linear real arithmetic
    LOGIC_NIRA, // non-linear mixed arithmetic
    LOGIC_RDL,  // real difference logic
    LOGIC_UF,   // uninterpreted functions

    //  Arrays + some other theory
    LOGIC_ABV,   // arrays + bitvectors
    LOGIC_ALIA,  // arrays + linear integer arithmetic
    LOGIC_ALRA,  // arrays + linear real arithmetic
    LOGIC_ALIRA, // arrays + mixed linear arithmetic
    LOGIC_ANIA,  // arrays + non-linear integer arithmetic
    LOGIC_ANRA,  // arrays + non-linear real arithmetic
    LOGIC_ANIRA, // arrays + mixed/non-linear arithmetic
    LOGIC_AUF,   // arrays + uninterpreted functions

    //  Uninterpreted function + another theory
    LOGIC_UFBV,    // uninterpreted functions + bitvectors
    LOGIC_UFBVLIA, // uninterpreted functions + bitvectors + linear integer
                   // arithmetic
    LOGIC_UFIDL,   // uninterpreted functions + integer difference logic
    LOGIC_UFLIA,   // uninterpreted functions + linear integer arithmetic
    LOGIC_UFLRA,   // uninterpreted functions + linear real arithmetic
    LOGIC_UFLIRA,  // uninterpreted functions + mixed linear arithmetic
    LOGIC_UFNIA,   // uninterpreted functions + non-linear integer arithmetic
    LOGIC_UFNRA,   // uninterpreted functions + non-linear real arithmetic
    LOGIC_UFNIRA,  // uninterpreted functions + mixed, non-linear arithmetic
    LOGIC_UFRDL,   // uninterpreted functions + real difference logic

    //  Arrays + uninterpreted functions + another theory
    LOGIC_AUFBV,    // arrays + uninterpreted functions + bitvectors
    LOGIC_AUFBVLIA, // arrays + uninterpreted functions + bitvectors + linear
                    // integer arithmetic
    LOGIC_AUFBVNIA, // arrays + uninterpreted functions + bitvectors + nonlinear
                    // integer arithmetic
    LOGIC_AUFLIA,   // arrays + uninterpreted functions + linear integer
                    // arithmetic
    LOGIC_AUFLRA,   // arrays + uninterpreted functions + linear real arithmetic
    LOGIC_AUFLIRA, // arrays + uninterpreted functions + mixed linear arithmetic
    LOGIC_AUFNIA,  // arrays + uninterpreted functions + non-linear integer
                   // arithmetic
    LOGIC_AUFNRA,  // arrays + uninterpreted functions + non-linear real
                   // arithmetic
    LOGIC_AUFNIRA, // arrays + uninterpreted functions + mixed, non-linear
                   // arithmetic

    /*
     * Quantifier-free fragments
     */
    LOGIC_QF_AX,   // arrays
    LOGIC_QF_BV,   // bitvectors
    LOGIC_QF_IDL,  // integer difference logic
    LOGIC_QF_LIA,  // linear integer arithmetic
    LOGIC_QF_LRA,  // linear real arithmetic
    LOGIC_QF_LIRA, // mixed linear arithmetic
    LOGIC_QF_NIA,  // non-linear integer arithmetic
    LOGIC_QF_NRA,  // non-linear real arithmetic
    LOGIC_QF_NIRA, // non-linear mixed arithmetic
    LOGIC_QF_RDL,  // real difference logic
    LOGIC_QF_UF,   // uninterpreted functions

    //  Arrays + some other theory
    LOGIC_QF_ABV,   // arrays + bitvectors
    LOGIC_QF_ALIA,  // arrays + linear integer arithmetic
    LOGIC_QF_ALRA,  // arrays + linear real arithmetic
    LOGIC_QF_ALIRA, // arrays + mixed linear arithmetic
    LOGIC_QF_ANIA,  // arrays + non-linear integer arithmetic
    LOGIC_QF_ANRA,  // arrays + non-linear real arithmetic
    LOGIC_QF_ANIRA, // arrays + mixed/non-linear arithmetic
    LOGIC_QF_AUF,   // arrays + uninterpreted functions

    //  Uninterpreted function + another theory
    LOGIC_QF_UFBV,    // uninterpreted functions + bitvectors
    LOGIC_QF_UFBVLIA, // uninterpreted functions + bitvectors + linear integer
                      // arithmetic
    LOGIC_QF_UFIDL,   // uninterpreted functions + integer difference logic
    LOGIC_QF_UFLIA,   // uninterpreted functions + linear integer arithmetic
    LOGIC_QF_UFLRA,   // uninterpreted functions + linear real arithmetic
    LOGIC_QF_UFLIRA,  // uninterpreted functions + mixed linear arithmetic
    LOGIC_QF_UFNIA,   // uninterpreted functions + non-linear integer arithmetic
    LOGIC_QF_UFNRA,   // uninterpreted functions + non-linear real arithmetic
    LOGIC_QF_UFNIRA,  // uninterpreted functions + mixed, non-linear arithmetic
    LOGIC_QF_UFRDL,   // uninterpreted functions + real difference logic

    //  Arrays + uninterpreted functions + another theory
    LOGIC_QF_AUFBV,    // arrays + uninterpreted functions + bitvectors
    LOGIC_QF_AUFBVLIA, // arrays + uninterpreted functions + bitvectors + linear
                       // integer arithmetic
    LOGIC_QF_AUFBVNIA, // arrays + uninterpreted functions + bitvectors +
                       // nonlinear integer arithmetic
    LOGIC_QF_AUFLIA,   // arrays + uninterpreted functions + linear integer
                       // arithmetic
    LOGIC_QF_AUFLRA,   // arrays + uninterpreted functions + linear real
                       // arithmetic
    LOGIC_QF_AUFLIRA,  // arrays + uninterpreted functions + mixed linear
                       // arithmetic
    LOGIC_QF_AUFNIA,   // arrays + uninterpreted functions + non-linear integer
                       // arithmetic
    LOGIC_QF_AUFNRA,   // arrays + uninterpreted functions + non-linear real
                       // arithmetic
    LOGIC_QF_AUFNIRA,  // arrays + uninterpreted functions + mixed, non-linear
                       // arithmetic

    LOGIC_NONE,
    LOGIC_ALL,
    LOGIC_UNKNOWN,
} logic_t;

typedef struct symbol_table_entry {
    symbol_kind_t kind;
    uint32_t num_parameters;
} symbol_table_entry_t;

// A rank is a list of sorts with the last element being the return sort.
typedef sort_t *rank_t;

/**
 * Stores information on symbols and their interpretations.
 *
 * Note: we don't allow shadowing of sort/function/system symbols.
 */
typedef struct context {

    logic_t current_logic;

    /**
     * Maps symbols to their kind. Use this to track all symbols currently in
     * use and which table to perform an actual lookup (e.g., `sort_table`,
     * `function_table`, etc.).
     */
    string_int_map_t symbol_table;

    /**
     * Maps sort symbols to their number of parameters and definition. If a sort
     * is uninterpreted (i.e., has no definition), then its definition is NULL.
     */
    string_map_t sort_table;

    /**
     * Maps variable symbols to their kind (input, output, local) and sort.
     */
    string_map_t var_table;

    /**
     * Maps function symbols to their signature and definition. If a function is
     * uninterpreted (i.e., has no definition), then its definition is NULL.
     */
    string_map_t fun_table;

    /**
     * Maps systems to their signature.
     */
    string_map_t sys_table;

} context_t;

void init_context(context_t *context);
void delete_context(context_t *context);

symbol_kind_t context_find(context_t *context, char *symbol);

bool context_add_function_symbol(context_t *context, char *symbol,
                                 rank_t rank, uint32_t rank_size);
bool context_remove_function_symbol(context_t *context, char *symbol);
bool context_add_sort_symbol(context_t *context, char *symbol);
bool context_add_system_symbol(context_t *context, char *symbol);

/**
 * Adds `symbol |-> sort` to the context and fails if `symbol` is already in the
 * context. Returns true on success and false on failure.
 */
bool context_add_var_symbol(context_t *context, char *symbol, sort_t *sort);

sort_list_entry_t *context_get_var_symbols(context_t *context);
sort_t *context_find_var_symbol(context_t *context, char *symbol);
void context_reset_var_symbols(context_t *context);

void set_current_logic(context_t *context, logic_t logic);

#endif