/**
 *
 */
#ifndef __STR_MAP_H__
#define __STR_MAP_H__

#include <stdint.h>
#include <stdlib.h>

typedef struct str_map_entry str_map_entry_t;

/**
 * Each entry in the string map stores the string, a void pointer value, and the
 * next entry in the bucket.
 */
struct str_map_entry {
    char *str;
    void *value;
    str_map_entry_t *next;
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
typedef struct str_map {
    str_map_entry_t **data;
    uint32_t capacity;
    void (*delete_value)(void *);
} str_map_t;

#define DEFAULT_STR_MAP_SIZE 1024

void init_str_map(str_map_t *map, uint32_t size, void (*delete_value)(void *));
void delete_str_map(str_map_t *map);
void str_map_reset(str_map_t *map);
void *str_map_find(str_map_t *map, char *string);
void str_map_add(str_map_t *map, char *string, size_t n, void *value);
void *str_map_remove(str_map_t *map, char *string);

#endif
