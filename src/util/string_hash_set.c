/**
 * 
*/
#include <stdlib.h>

#include "util/hash.h"
#include "util/string_hash_set.h"


/**
 * Compute the hash value for `symbol` relative to the size of `set`. Since `set`'s size is a
 * power of 2, we just return the lowest `log2(set->size)-1` bits of `symbol`'s hash.
*/
uint32_t compute_string_set_entry_hash(string_set_t *set, char *symbol)
{
    uint32_t mask = set->size - 1;
    return mask & djb2_hash_string(symbol);
}


void init_string_set(string_set_t *set, uint32_t size)
{
    if (size <= 0) {
        set->size = DEFAULT_STRING_SET_SIZE;
    } else {
        set->size = size;
    }

    set->data = malloc(set->size * sizeof(string_set_entry_t *)); 
    
    uint32_t i;
    for(i = 0; i < set->size; ++i) {
        set->data[i] = NULL;
    }
}


bool string_set_contains(string_set_t *set, char *str)
{
    uint32_t hash;
    
    hash = compute_string_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        return false;
    }

    string_set_entry_t *cur;
    for(cur = set->data[hash]; cur != NULL; cur = cur->next) {
        if (!strcmp(cur->value, str)) {
            return true;
        }
    }

    return false;
}


void string_set_add(string_set_t *set, char *str)
{
    string_set_entry_t *entry;
    uint32_t hash;

    entry = malloc(sizeof(string_set_entry_t));
    entry->value = str;
    entry->next = NULL;

    hash = compute_string_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        set->data[hash] = entry;
        return;
    }

    string_set_entry_t *cur;
    for(cur = set->data[hash]; cur->next != NULL; cur = cur->next);
    cur->next = entry;
}


/**
 * Returns `true` on success, `false` otherwise.
*/
bool string_set_remove(string_set_t *set, char *str)
{
    uint32_t hash;
    
    hash = compute_string_set_entry_hash(set, str);

    if (set->data[hash] == NULL) {
        return -1;
    }

    string_set_entry_t **cur, *prev;

    cur = &set->data[hash];
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

        return (int64_t) hash;
    }

    return -1;

}

