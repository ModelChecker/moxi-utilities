/**
 *
 */
#ifndef __STRING_INT_MAP_H__
#define __STRING_INT_MAP_H__

#include <stdint.h>
#include <stdlib.h>

typedef struct str_int_map_entry str_int_map_entry_t;

/**
 * Each entry in the string map stores the string, an integer value, and the
 * next entry in the bucket.
 */
struct str_int_map_entry {
    char *string;
    int value;
    str_int_map_entry_t *next;
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
typedef struct str_int_map {
    str_int_map_entry_t **data;
    uint32_t capacity;
} str_int_map_t;

#define DEFAULT_STR_INT_MAP_SIZE 1024

void init_str_int_map(str_int_map_t *map, uint32_t size);
void delete_str_int_map(str_int_map_t *map);
void str_int_map_reset(str_int_map_t *map);
int str_int_map_find(str_int_map_t *map, char *string);
void str_int_map_add(str_int_map_t *map, char *string, size_t n, int value);
int str_int_map_remove(str_int_map_t *map, char *string);

#endif