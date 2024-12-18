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
    term_t var;
} var_table_entry_t;

static inline bool str_is_primed(const char *str, size_t len)
{
    return str[len - 1] == '\'';
}

typedef struct system {
    char *name;
    uint32_t ninput;
    sort_t *input;
    uint32_t noutput;
    sort_t *output;
} system_t;

/**
 * Stores information on symbols and their interpretations.
 *
 * The context stores the following tables:
 * - term_table: maps strings to user-defined term symbols
 * - var_table: maps strings to variable kinds and sorts
 * - sys_table: maps strings to the system signatures
 */
typedef struct moxi_context {
    const logic_t *logic;
    bool active_symbols[NUM_SYMBOLS];

    str_map_t sort_table;
    str_map_t term_table; // table for user-defined terms
    str_map_t sys_table;  // table for defined systems

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

bool set_current_logic(moxi_context_t *ctx, char *symbol);

/*******************************************************************************
 * Term Management
 *
 * - Add functions/constants to the context.
 * - Find terms in the context.
 ******************************************************************************/
bool moxi_declare_fun(moxi_context_t *ctx, char *symbol, uint32_t nargs,
                      sort_t *args, sort_t ret);
bool moxi_define_fun(moxi_context_t *ctx, char *symbol, uint32_t nargs,
                     sort_t *args, sort_t ret, term_t body);
const symbol_t *moxi_find_term(moxi_context_t *ctx, char *str);

/*******************************************************************************
 * Scope Management
 *
 * - Push/pop scopes.
 * - Add variables to the context and current scope.
 * - Find variables in the context.
 ******************************************************************************/
void moxi_push_scope(moxi_context_t *ctx);
void moxi_pop_scope(moxi_context_t *ctx);
bool moxi_add_var(moxi_context_t *ctx, char *str, var_kind_t kind, sort_t sort);
var_table_entry_t *moxi_find_var(moxi_context_t *ctx, char *str);

/*******************************************************************************
 * Sort Management
 *
 * - Add sorts to the context.
 * - Find sorts in the context.
 ******************************************************************************/
bool moxi_declare_sort(moxi_context_t *ctx, char *str, uint32_t arity);
void moxi_define_sort(moxi_context_t *ctx, char *str, uint32_t nargs,
                      sort_t *args, sort_t body);
const symbol_t *moxi_find_sort(moxi_context_t *ctx, char *str);

/*******************************************************************************
 * System Management
 ******************************************************************************/
bool moxi_define_system(moxi_context_t *ctx, char *str, 
                        uint32_t ninput, sort_t *input,
                        uint32_t noutput, sort_t *output,
                        uint32_t nlocal, sort_t *local, 
                        term_t init, term_t trans, term_t inv);
bool moxi_define_system_subsys(moxi_context_t *ctx, char *str, 
                               uint32_t ninput, sort_t *input, 
                               uint32_t noutput, sort_t *output,
                               uint32_t nlocal, sort_t *local,
                               term_t init, term_t trans, term_t inv, 
                               uint32_t nsubsys, char **symbols, 
                               uint32_t *nsubsys_input, term_t **subsys_input, 
                               uint32_t *nsubsys_output, term_t **subsys_output);
bool moxi_check_system(moxi_context_t *ctx, char *str, uint32_t ninput,
                       sort_t *input, uint32_t noutput, sort_t *output,
                       uint32_t nlocal, uint32_t nassume, char **vassume, term_t *assume,
                       uint32_t nfair, char **vfair, term_t *fair, char **vreach, uint32_t nreach,
                       term_t *reach, uint32_t ncur, char **vcur, term_t *cur,
                       uint32_t nquery, char **vquery, term_t **query);
system_t *moxi_find_system(moxi_context_t *ctx, char *str);

#endif