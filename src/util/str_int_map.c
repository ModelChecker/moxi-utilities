#include <string.h>

#include "util/hash.h"
#include "util/str_int_map.h"

/**
 * Compute the hash symbol for `symbol` relative to the size of `map`. Since
 * `map`'s size is a power of 2, we just return the lowest
 * `log2(map->capacity)-1` bits of `symbol`'s hash.
 */
uint32_t compute_str_int_map_entry_hash(str_int_map_t *map, char *symbol)
{
    uint32_t mask = 0, ret = 0;
    
    mask = map->capacity - 1;
    ret = mask & djb2_hash_string(symbol);
    return ret;
}

void init_str_int_map(str_int_map_t *map, uint32_t size)
{
    map->capacity = size <= 0 ? DEFAULT_STR_INT_MAP_SIZE : size; 
    map->data = calloc(map->capacity, sizeof(str_int_map_entry_t *));
}

void delete_str_int_map(str_int_map_t *map)
{
    str_int_map_reset(map);
    free(map->data);
}

void str_int_map_reset(str_int_map_t *map)
{
    uint32_t i;
    str_int_map_entry_t *cur, *next;

    for (i = 0; i < map->capacity; ++i) {
        cur = map->data[i];
        if (cur == NULL) {
            continue;
        }

        next = cur->next;
        while (cur != NULL) {
            free(cur->str);
            free(cur);
            cur = next;
            next = next->next;
        }
    }
}

/**
 * Returns the value for `symbol` if `symbol` is present in `map`. Otherwise,
 * returns -1.
 */
int str_int_map_find(str_int_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_str_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return -1;
    }

    str_int_map_entry_t *cur;
    for (cur = map->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->str, symbol)) {
            return cur->value;
        }
    }

    return -1;
}

/**
 *
 */
void str_int_map_add(str_int_map_t *map, char *symbol, size_t n, int value)
{
    str_int_map_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(str_int_map_entry_t));
    entry->str = malloc(sizeof(char) * n + 1);
    strncpy(entry->str, symbol, n + 1);
    entry->value = value;
    entry->next = NULL;

    hash = compute_str_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        map->data[hash] = entry;
        return;
    }

    str_int_map_entry_t *cur;
    for (cur = map->data[hash]; cur->next != NULL; cur = cur->next)
        ;
    cur->next = entry;
}

/**
 * Returns the value of `symbol` on success, -1 on failure.
 */
int str_int_map_remove(str_int_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_str_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return -1;
    }

    str_int_map_entry_t **cur, *prev;
    int value;

    prev = NULL;

    for (cur = &map->data[hash]; *cur != NULL;
         prev = *cur, cur = &(*cur)->next) {
        if (strcmp((*cur)->str, symbol)) {
            continue;
        }

        value = (*cur)->value;

        if (prev == NULL) {
            *cur = NULL;
        } else {
            prev->next = (*cur)->next;
            free((*cur)->str);
            free(*cur);
        }

        return value;
    }

    return -1;
}