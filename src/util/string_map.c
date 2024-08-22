#include <string.h>

#include "util/hash.h"
#include "util/string_map.h"

/**
 * Compute the hash symbol for `symbol` relative to the size of `map`. Since
 * `map`'s size is a power of 2, we just return the lowest
 * `log2(map->size)-1` bits of `symbol`'s hash.
 */
uint32_t compute_string_map_entry_hash(string_map_t *map, char *symbol)
{
    uint32_t mask = map->size - 1;
    return mask & djb2_hash_string(symbol);
}

void init_string_map(string_map_t *map, uint32_t size)
{
    if (size <= 0) {
        map->size = DEFAULT_SYMBOL_TABLE_SIZE;
    } else {
        map->size = size;
    }

    map->data = malloc(map->size * sizeof(string_map_entry_t *));

    uint32_t i;
    for (i = 0; i < map->size; ++i) {
        map->data[i] = NULL;
    }
}

void delete_string_map(string_map_t *map)
{
    uint32_t i;
    string_map_entry_t *cur, *next;

    for (i = 0; i < map->size; ++i) {
        cur = map->data[i];
        if (cur == NULL) {
            continue;
        }

        next = cur->next;
        while (cur != NULL) {
            free(cur->string);
            free(cur);
            cur = next;
            next = next->next;
        }
    }

    free(map->data);
}

/**
 * Returns the value for `symbol` if `symbol` is present in `map`. Otherwise,
 * returns NULL.
 */
void *string_map_find(string_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_string_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return NULL;
    }

    string_map_entry_t *cur;
    for (cur = map->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->string, symbol)) {
            return cur->value;
        }
    }

    return NULL;
}

/**
 *
 */
void string_map_add(string_map_t *map, char *symbol, void *value)
{
    string_map_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(string_map_entry_t));
    entry->string = malloc(sizeof(char) * strlen(symbol));
    strcpy(entry->string, symbol);
    entry->value = value;
    entry->next = NULL;

    hash = compute_string_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        map->data[hash] = entry;
        return;
    }

    string_map_entry_t *cur;
    for (cur = map->data[hash]; cur->next != NULL; cur = cur->next)
        ;
    cur->next = entry;
}

/**
 * Returns the value of `symbol` on success, NULL on failure.
 */
void *string_map_remove(string_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_string_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return NULL;
    }

    string_map_entry_t **cur, *prev;
    void *value;

    prev = NULL;

    for (cur = &map->data[hash]; *cur != NULL;
         prev = *cur, cur = &(*cur)->next) {
        if (strcmp((*cur)->string, symbol)) {
            continue;
        }

        value = (*cur)->value;

        if (prev == NULL) {
            *cur = NULL;
        } else {
            prev->next = (*cur)->next;
            free((*cur)->string);
            free(*cur);
        }

        return value;
    }

    return NULL;
}
