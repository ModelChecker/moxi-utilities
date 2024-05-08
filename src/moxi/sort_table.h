/**
 * 
*/
#ifndef __SORT_TABLE_H__
#define __SORT_TABLE_H__

#include "util/string_pair_list.h"

typedef struct sort_table_entry sort_table_entry_t;

struct sort_table_entry {
    char *symbol;
    // string_list_t *params;
};


/**
 * Maps sort symbols to their parameter list. 
 *
 *  "sort-id" -> arity
*/
typedef struct sort_table {
    sort_table_entry_t **data;
    uint32_t size;
} sort_table_t;

#define DEFAULT_SORT_TABLE_SIZE 512


void init_sort_table(sort_table_t *table, uint32_t size);
void delete_sort_table(sort_table_t *table);
string_pair_list_t *sort_table_find(sort_table_t *table, char *symbol);
void sort_table_add(sort_table_t *table, char *symbol);
void sort_table_remove(sort_table_t *table, char *symbol);


#endif