/**
 * 
*/
#ifndef __FUNCTION_TABLE_H__
#define __FUNCTION_TABLE_H__

#include "util/string_pair_list.h"
#include "moxi/terms.h"
#include "moxi/sorts.h"

typedef struct function_table_entry function_table_entry_t;

struct function_table_entry {
    char *symbol;
    sort_t *rank;
    uint32_t nargs; // len(rank) = nargs + 1
    term_t *body;
    function_table_entry_t *next;
};


/**
 * Maps user-defined function symbols to their rank and term, if available. A rank is a list of
 * sort/variable symbol pairs with the tail of the list being the return sort. Its term is
 * unavailable (NULL) if it is an uninterpreted function.
 * 
 * Also, if a function symbol is in the symbol table but not the function table, then it is a
 * predefined (logic) function.
 *
 * "fun-id" -> (<symbol>, [<arg-sort-1>, ..., <arg-sort-n>, <return-sort>], <term>)
*/
typedef struct function_table {
    function_table_entry_t **data;
    uint32_t size;
} function_table_t;

#define DEFAULT_FUNCTION_TABLE_SIZE 512


void init_function_table(function_table_t *table, uint32_t size);
void delete_function_table(function_table_t *table);
string_pair_list_t *function_table_find(function_table_t *table, char *symbol);
void function_table_add(function_table_t *table, char *symbol, sort_t *rank, uint32_t nargs, term_t *term);
void function_table_remove(function_table_t *table, char *symbol);


#endif