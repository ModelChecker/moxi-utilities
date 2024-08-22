/**
 *
 */
#ifndef __SYMBOL_TABLE_H__
#define __SYMBOL_TABLE_H__

#include <stdint.h>
#include <stdlib.h>

typedef struct string_map_entry string_map_entry_t;

/**
 * Each entry in the string map stores the string, a void pointer value, and the
 * next entry in the bucket.
 */
struct string_map_entry {
    char *string;
    void *value;
    string_map_entry_t *next;
};

/**
 * A string map is a hash map of string map entries. Each bucket (uniquely
 * hashed entry) in the string map is a linked list, where the string map entry
 * stores the next entry in the list.
 *
 * map[0]    = <"A",value> -> <"B",value> -> ...
 * ...
 * map[size] = <"C",value> -> <"D",value> -> ...
 */
typedef struct string_map {
    string_map_entry_t **data;
    uint32_t size;
} string_map_t;

#define DEFAULT_SYMBOL_TABLE_SIZE 1024

void init_string_map(string_map_t *map, uint32_t size);
void delete_string_map(string_map_t *map);
void *string_map_find(string_map_t *map, char *string);
void string_map_add(string_map_t *map, char *string, void *value);
void *string_map_remove(string_map_t *map, char *string);

#endif