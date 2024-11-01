#ifndef __STRING_SET_H__
#define __STRING_SET_H__

#include <stdbool.h>
#include <stdint.h>

/**
 * A string set is a unordered set of char pointers. We use the hash function in
 * hash.h to create a hash map with a number of buckets (64 by default) where
 * each bucket is a linked list of strings.
 */

typedef struct str_set_entry str_set_entry_t;

struct str_set_entry {
    char *value;
    str_set_entry_t *next;
};

typedef struct str_set {
    str_set_entry_t **data;
    uint32_t capacity;
} str_set_t;

#define DEFAULT_STRING_SET_SIZE 64

void init_str_set(str_set_t *set, uint32_t size);
void delete_str_set(str_set_t *set);
bool str_set_contains(str_set_t *set, char *str);
void str_set_add(str_set_t *set, char *str);
bool str_set_remove(str_set_t *set, char *str);

#endif