/**
 *
 */
#ifndef __STRING_INT_MAP_H__
#define __STRING_INT_MAP_H__

#include <stdint.h>
#include <stdlib.h>

typedef struct string_int_map_entry string_int_map_entry_t;

/**
 * Each entry in the string map stores the string, an integer value, and the
 * next entry in the bucket.
 */
struct string_int_map_entry {
    char *string;
    int value;
    string_int_map_entry_t *next;
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
typedef struct string_int_map {
    string_int_map_entry_t **data;
    uint32_t size;
} string_int_map_t;

#define DEFAULT_SYMBOL_TABLE_SIZE 1024

void init_string_int_map(string_int_map_t *map, uint32_t size);
void delete_string_int_map(string_int_map_t *map);
int string_int_map_find(string_int_map_t *map, char *string);
void string_int_map_add(string_int_map_t *map, char *string, int value);
int string_int_map_remove(string_int_map_t *map, char *string);

#endif