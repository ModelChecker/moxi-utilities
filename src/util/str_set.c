/**
 * 
*/
#include <stdlib.h>
#include <string.h>

#include "util/hash.h"
#include "util/str_set.h"


/**
 * Compute the hash value for `symbol` relative to the size of `set`. Since `set`'s size is a
 * power of 2, we just return the lowest `log2(set->capacity)-1` bits of `symbol`'s hash.
*/
uint32_t compute_str_set_entry_hash(str_set_t *set, char *symbol)
{
    uint32_t mask = set->capacity - 1;
    return mask & djb2_hash_string(symbol);
}


void init_str_set(str_set_t *set, uint32_t size)
{
    if (size == 0) {
        set->capacity = DEFAULT_STRING_SET_SIZE;
    } else {
        set->capacity = size;
    }

    set->data = malloc(set->capacity * sizeof(str_set_entry_t *)); 
    
    uint32_t i;
    for(i = 0; i < set->capacity; ++i) {
        set->data[i] = NULL;
    }
}


bool str_set_contains(str_set_t *set, char *str)
{
    uint32_t hash;
    
    hash = compute_str_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        return false;
    }

    str_set_entry_t *cur;
    for(cur = set->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->value, str)) {
            return true;
        }
    }

    return false;
}


void str_set_add(str_set_t *set, char *str)
{
    str_set_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(str_set_entry_t));
    entry->value = str;
    entry->next = NULL;

    hash = compute_str_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        set->data[hash] = entry;
        return;
    }

    str_set_entry_t *cur;
    for(cur = set->data[hash]; cur->next != NULL; cur = cur->next);
    cur->next = entry;
}


/**
 * Returns `true` on success, `false` otherwise.
*/
bool str_set_remove(str_set_t *set, char *str)
{
    uint32_t hash;
    
    hash = compute_str_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        return -1;
    }

    str_set_entry_t **cur, *prev;

    prev = NULL;

    for(cur = &set->data[hash]; *cur != NULL; prev = *cur, cur = &(*cur)->next) {
        if(strcmp((*cur)->value, str)) {
            continue;
        }

        if (prev == NULL) {
            *cur = NULL;
        } else {
            prev->next = (*cur)->next;
            free(*cur);
        }

        return true;
    }

    return false;
}

