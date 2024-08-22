#ifndef __STRING_SET_H__
#define __STRING_SET_H__

#include <stdbool.h>
#include <stdint.h>

/**
 * A string set is a unordered set of char pointers. We use the hash function in
 * hash.h to create a hash map with a number of buckets (64 by default) where
 * each bucket is a linked list of strings.
 */

typedef struct string_set_entry string_set_entry_t;

struct string_set_entry {
    char *value;
    string_set_entry_t *next;
};

typedef struct string_set {
    string_set_entry_t **data;
    uint32_t size;
} string_set_t;

#define DEFAULT_STRING_SET_SIZE 64

void init_string_set(string_set_t *set, uint32_t size);
void delete_string_set(string_set_t *set);
bool string_set_contains(string_set_t *set, char *str);
void string_set_add(string_set_t *set, char *str);
bool string_set_remove(string_set_t *set, char *str);

#endif