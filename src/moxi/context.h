/**
 *
 */
#ifndef __CONTEXT_H__
#define __CONTEXT_H__

#include <stdbool.h>
#include <yices.h>

#include "moxi/logic.h"
#include "parse/token.h"
#include "util/stack.h"
#include "util/str_int_map.h"
#include "util/str_map.h"
#include "util/str_vector.h"

// A MoXI sort is a Yices type
typedef type_t sort_t;

// typedef struct sort_table_entry {
//     char *symbol;
//     uint32_t len;
//     theory_symbol_type_t thy_sym_type;
// } sort_table_entry_t;

// typedef struct term_table_entry {
//     char *symbol;
//     uint32_t len;
//     theory_symbol_type_t thy_sym_type;
//     bool is_var;
// } term_table_entry_t;

typedef enum {
    INPUT_VAR,
    OUTPUT_VAR,
    LOCAL_VAR,
    LOGIC_VAR // Let-bound, quantified, and define-fun variables (can not be
              // primed)
} var_kind_t;

// Stores a variable's kind and sort
typedef struct var_table_entry {
    var_kind_t kind;
    term_t term;
    bool is_primed;
} var_table_entry_t;

static inline bool symbol_is_primed(const char *str, uint32_t len)
{
    return str[len - 1] == '\'';
}

typedef struct sys_table_entry {
    char *name;
    uint32_t len;
    uint32_t ninput;
    sort_t *input;
    uint32_t noutput;
    sort_t *output;
    uint32_t nlocal;
    sort_t *local;
} sys_table_entry_t;

/**
 * Stores information on symbols and their interpretations.
 *
 * The context stores the following tables:
 * - sys_table: maps strings to the system signatures
 */
typedef struct moxi_context {
    int status;
    const logic_t *logic;
    bool active_theory_symbols[NUM_THEORY_SYMBOLS];

    // Table for defined systems
    str_map_t sys_table;

    // Maps variable symbols to their kind (input, output, local) and sort.
    str_map_t var_table;

    // Stack of string vectors for storing scoped variables. When a new scope is
    // entered, a new string vector is pushed onto the stack. When a scope is
    // exited, the top string vector is popped off the stack and all variables
    // in the top vector are removed from the context.
    vstack_t scope_stack;
} moxi_context_t;

void init_context(moxi_context_t *ctx);
void delete_context(moxi_context_t *ctx);

void moxi_set_logic(moxi_context_t *ctx, char *symbol);

bool is_active_theory_term(const moxi_context_t *ctx, const char *symbol);
bool is_active_theory_sort(const moxi_context_t *ctx, const char *symbol);
bool is_active_term(const moxi_context_t *ctx, const char *symbol);
bool is_active_sort(const moxi_context_t *ctx, const char *symbol);
theory_symbol_type_t get_theory_symbol_type(const char *symbol);

/*******************************************************************************
 * Term Management
 *
 * - Add functions/constants to the context.
 * - Find terms in the context.
 ******************************************************************************/
void moxi_declare_fun(moxi_context_t *ctx, char *symbol, uint32_t nargs,
                      sort_t *args, sort_t ret);
void moxi_define_fun(moxi_context_t *ctx, char *symbol, uint32_t nargs,
                     sort_t *args, sort_t ret, term_t body);

/*******************************************************************************
 * Scope Management
 *
 * - Push/pop scopes.
 * - Add variables to the context and current scope.
 * - Find variables in the context.
 ******************************************************************************/
void moxi_push_scope(moxi_context_t *ctx);
void moxi_pop_scope(moxi_context_t *ctx);
str_vector_t *moxi_get_scope(moxi_context_t *ctx);
void moxi_add_named_term(moxi_context_t *ctx, char *str, term_t term, var_kind_t kind);
const var_table_entry_t *moxi_find_var(moxi_context_t *ctx, char *symbol);

/*******************************************************************************
 * Sort Management
 *
 * - Add sorts to the context.
 * - Find sorts in the context.
 ******************************************************************************/
void moxi_declare_sort(moxi_context_t *ctx, char *str, uint32_t arity);
void moxi_declare_enum_sort(moxi_context_t *ctx, char *str, uint32_t nvalues, char **values);
void moxi_define_sort(moxi_context_t *ctx, char *str, uint32_t nargs,
                      sort_t *args, sort_t body);

/*******************************************************************************
 * System Management
 ******************************************************************************/
void moxi_define_system(moxi_context_t *ctx, char *str, 
                        uint32_t ninput, sort_t *input,
                        uint32_t noutput, sort_t *output,
                        uint32_t nlocal, sort_t *local);
void moxi_define_system_subsys(moxi_context_t *ctx, char *str, 
                               uint32_t ninput, sort_t *input, 
                               uint32_t noutput, sort_t *output,
                               uint32_t nlocal, sort_t *local,
                               term_t init, term_t trans, term_t inv, 
                               uint32_t nsubsys, char **symbols, 
                               uint32_t *nsubsys_input, term_t **subsys_input, 
                               uint32_t *nsubsys_output, term_t **subsys_output);
const sys_table_entry_t *moxi_find_system(moxi_context_t *ctx, char *str);

#endif
