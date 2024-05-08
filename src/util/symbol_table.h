/**
 * 
*/
#ifndef __SYMBOL_TABLE_H__
#define __SYMBOL_TABLE_H__

#include <stdint.h>
#include <stdlib.h>


typedef struct symbol_table_entry symbol_table_entry_t;

/**
 * 
*/
struct symbol_table_entry {
    char *symbol;
    uint32_t value; // Useful for enums
    symbol_table_entry_t *next;
};


/**
 * A symbol table is a hash map of symbol table entries. Each bucket (uniquely hashed entry) in the
 * symbol table is a linked list, where the symbol table entry stores the next entry in the list.
 *
 * table[0]    = <"A",0> -> <"B",1> -> ...
 * ...
 * table[size] = <"C",2> -> <"D",1> -> ...
*/
typedef struct symbol_table {
    symbol_table_entry_t **data;
    uint32_t size; 
} symbol_table_t;

#define DEFAULT_SYMBOL_TABLE_SIZE 1024


void init_symbol_table(symbol_table_t *table, uint32_t size);
void delete_symbol_table(symbol_table_t *table);
int64_t symbol_table_find(symbol_table_t *table, char *symbol);
void symbol_table_add(symbol_table_t *table, char *symbol, uint32_t value);
int64_t symbol_table_remove(symbol_table_t *table, char *symbol);


#endif