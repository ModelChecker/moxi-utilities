#include <string.h>

#include "util/hash.h"
#include "util/int_map.h"

void init_int_map(int_map_t *map, uint32_t size)
{
    map->capacity = size <= 0 ? DEFAULT_INT_MAP_SIZE : size; 
    map->data = calloc(map->capacity, sizeof(int_map_entry_t));
}

void delete_int_map(int_map_t *map)
{
    uint32_t i;
    for (i = 0; i < map->capacity; ++i) {
        if (map->data[i].value != NULL) {
            free(map->data[i].value);
        }
    }
    free(map->data);
}

/**
 * Returns the value for `key` if `key` is present in `map`. Returns NULL if
 * nothing is present.
 */
void *int_map_find(int_map_t *map, uint32_t key)
{
    uint32_t hash = key & (map->capacity - 1);
    return map->data[hash].value;
}

/**
 * Adds `value` to `map` with key `key`, overwriting any existing value. Returns
 * the old value.
 */
void *int_map_add(int_map_t *map, uint32_t key, void *value)
{
    int_map_entry_t *entry;
    entry = malloc(sizeof(int_map_entry_t));
    entry->key = key;
    entry->value = value;

    uint32_t hash = key & (map->capacity - 1);

    if (map->data[hash].value == NULL) {
        map->data[hash].key = key;
        map->data[hash].value = value;
        return NULL;
    }

    void *old = map->data[hash].value;
    map->data[hash].value = value;
    return old;
}

/**
 * Returns the value for `key` if `key` is present in `map` and sets its value
 * to NULL. Otherwise, returns NULL.
 * 
 * Caller is responsible for freeing the returned value.
 */
void *int_map_remove(int_map_t *map, uint32_t key)
{
    uint32_t hash = key & (map->capacity - 1);
    if (map->data[hash].value == NULL) {
        return NULL;
    }
    void *old = map->data[hash].value;
    map->data[hash].value = NULL;
    return old;
}
