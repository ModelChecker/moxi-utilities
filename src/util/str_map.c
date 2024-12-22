#include <string.h>
#include <stdio.h>

#include "util/hash.h"
#include "util/str_map.h"

/**
 * Compute the hash symbol for `symbol` relative to the size of `map`. Since
 * `map`'s size is a power of 2, we just return the lowest
 * `log2(map->capacity)-1` bits of `symbol`'s hash.
 */
uint32_t compute_str_map_entry_hash(str_map_t *map, char *symbol)
{
    uint32_t mask = map->capacity - 1;
    return mask & djb2_hash_string(symbol);
}

void init_str_map(str_map_t *map, uint32_t size, void (*delete_value)(void *))
{
    map->capacity = size <= 0 ? DEFAULT_STR_MAP_SIZE : size; 
    map->data = calloc(map->capacity, sizeof(str_map_entry_t*));
    map->delete_value = delete_value;
}

void delete_str_map(str_map_t *map)
{
    str_map_reset(map);
    free(map->data);
}

void str_map_reset(str_map_t *map)
{
    uint32_t i;
    str_map_entry_t *cur, *next;
    for (i = 0; i < map->capacity; ++i) {
        cur = map->data[i];
        if (cur == NULL) {
            continue;
        }
        next = cur->next;
        while (cur != NULL) {
            map->delete_value(cur->value);
            free(cur->str);
            free(cur);
            cur = next;
            next = next->next;
        }
    }
}

/**
 * Returns the value for `symbol` if `symbol` is present in `map`. Otherwise,
 * returns NULL.
 */
void *str_map_find(str_map_t *map, char *symbol)
{
    uint32_t hash;
    hash = compute_str_map_entry_hash(map, symbol);
    if (map->data[hash] == NULL) {
        return NULL;
    }
    str_map_entry_t *cur;
    for (cur = map->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->str, symbol)) {
            return cur->value;
        }
    }
    return NULL;
}

/**
 *
 */
void str_map_add(str_map_t *map, char *symbol, size_t n, void *value)
{
    str_map_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(str_map_entry_t));
    entry->str = malloc(sizeof(char) * n + 1);
    strncpy(entry->str, symbol, n + 1);
    entry->value = value;
    entry->next = NULL;

    hash = compute_str_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        map->data[hash] = entry;
        return;
    }

    str_map_entry_t *cur;
    for (cur = map->data[hash]; cur->next != NULL; cur = cur->next)
        ;
    cur->next = entry;
}

/**
 * Returns the value of `symbol` on success, NULL on failure.
 */
void *str_map_remove(str_map_t *map, char *symbol)
{
    uint32_t hash;
    hash = compute_str_map_entry_hash(map, symbol);
    if (map->data[hash] == NULL) {
        return NULL;
    }
    str_map_entry_t **cur, *prev;
    void *value;
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

    return NULL;
}
