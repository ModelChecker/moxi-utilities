#include <string.h>

#include "util/hash.h"
#include "util/string_int_map.h"

/**
 * Compute the hash symbol for `symbol` relative to the size of `map`. Since
 * `map`'s size is a power of 2, we just return the lowest
 * `log2(map->size)-1` bits of `symbol`'s hash.
 */
uint32_t compute_string_int_map_entry_hash(string_int_map_t *map, char *symbol)
{
    uint32_t mask = 0, ret = 0;
    
    mask = map->size - 1;
    ret = mask & djb2_hash_string(symbol);
    return ret;
}

void init_string_int_map(string_int_map_t *map, uint32_t size)
{
    if (size <= 0) {
        map->size = DEFAULT_SYMBOL_TABLE_SIZE;
    } else {
        map->size = size;
    }

    map->data = malloc(map->size * sizeof(string_int_map_entry_t *));

    uint32_t i;
    for (i = 0; i < map->size; ++i) {
        map->data[i] = NULL;
    }
}

void delete_string_int_map(string_int_map_t *map)
{
    uint32_t i;
    string_int_map_entry_t *cur, *next;

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
 * returns -1.
 */
int string_int_map_find(string_int_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_string_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return -1;
    }

    string_int_map_entry_t *cur;
    for (cur = map->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->string, symbol)) {
            return cur->value;
        }
    }

    return -1;
}

/**
 *
 */
void string_int_map_add(string_int_map_t *map, char *symbol, int value)
{
    string_int_map_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(string_int_map_entry_t));
    entry->string = malloc(sizeof(char) * strlen(symbol));
    strcpy(entry->string, symbol);
    entry->value = value;
    entry->next = NULL;

    hash = compute_string_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        map->data[hash] = entry;
        return;
    }

    string_int_map_entry_t *cur;
    for (cur = map->data[hash]; cur->next != NULL; cur = cur->next)
        ;
    cur->next = entry;
}

/**
 * Returns the value of `symbol` on success, -1 on failure.
 */
int string_int_map_remove(string_int_map_t *map, char *symbol)
{
    uint32_t hash;

    hash = compute_string_int_map_entry_hash(map, symbol);

    if (map->data[hash] == NULL) {
        return -1;
    }

    string_int_map_entry_t **cur, *prev;
    int value;

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

    return -1;
}
