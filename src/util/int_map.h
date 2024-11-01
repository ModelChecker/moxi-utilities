/**
 *
 */
#ifndef __INT_MAP_H__
#define __INT_MAP_H__

#include <stdint.h>
#include <stdlib.h>

typedef struct int_map_entry int_map_entry_t;

/**
 * Each entry in the string map stores the int key and a void pointer value.
 */
struct int_map_entry {
    uint32_t key;
    void *value;
};

/**
 * An integer map is a hash map of integer map entries.
 */
typedef struct int_map {
    int_map_entry_t *data;
    uint32_t capacity;
} int_map_t;

#define DEFAULT_INT_MAP_SIZE 1024

void init_int_map(int_map_t *map, uint32_t size);
void delete_int_map(int_map_t *map);
void *int_map_find(int_map_t *map, uint32_t key);
void *int_map_add(int_map_t *map, uint32_t key, void *value);
void *int_map_remove(int_map_t *map, uint32_t key);

#endif