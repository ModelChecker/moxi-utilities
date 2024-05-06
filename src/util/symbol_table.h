/**
 * 
*/
#ifndef __SYMBOL_TABLE_H__
#define __SYMBOL_TABLE_H__

#include <stdint.h>
#include <stdlib.h>


typedef enum symbol_type {
    MOXI_SYM_VARIABLE,
    MOXI_SYM_SORT,
    MOXI_SYM_FUNCTION
} symbol_type_t;


typedef struct symbol_table_entry symbol_table_entry_t;

typedef struct symbol_table_entry {
    char *value;
    symbol_type_t type;
    symbol_table_entry_t *next;
};


/**
 * A symbol table is a hash map of symbol table entries. Each bucket (uniquely hashed entry) in the
 * symbol table is a linked list, where the symbol table entry stores the next entry in the list.
 *
 * table[0]    = entry("A") -> entry("B") -> ...
 * ...
 * table[size] = entry("C") -> entry("D") -> ...
*/
typedef struct symbol_table {
    symbol_table_entry_t **data;
    uint32_t size; 
} symbol_table_t;

#define DEFAULT_SYMBOL_TABLE_SIZE 64


void init_symbol_table(symbol_table_t *table, uint32_t size);
void delete_symbol_table(symbol_table_t *table);
int64_t symbol_table_find(symbol_table_t *table, char *symbol);
void symbol_table_add(symbol_table_t *table, char *symbol);


#endif