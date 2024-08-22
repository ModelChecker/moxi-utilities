#ifndef __SORT_H__
#define __SORT_H__

#include <stddef.h>
#include <stdint.h>

typedef struct sort sort_t;

struct sort {
    char *symbol;
    uint64_t *indices;
    size_t num_indices;
    sort_t **params;
    size_t num_params;
};

bool is_equal_sort(sort_t *s1, sort_t *s2);

bool is_bool_sort(sort_t *sort);
bool is_int_sort(sort_t *sort);
bool is_real_sort(sort_t *sort);
bool is_bitvec_sort(sort_t *sort);
bool is_array_sort(sort_t *sort);

// Returns width of sort if it is a BitVec sort, 0 otherwise
uint64_t get_bitvec_width(sort_t *sort);

typedef struct sort_list_entry sort_list_entry_t;
struct sort_list_entry {
    sort_t *sort;
    sort_list_entry_t *next;
};

void init_sort(sort_t *sort, char *symbol, uint64_t indices[],
                size_t num_indices, sort_t *params[], size_t num_params);
void delete_sort(sort_t *sort);

sort_t *new_sort(char *symbol, sort_t *params[], size_t nparams);
sort_t *new_bool_sort();
sort_t *new_int_sort();
sort_t *new_real_sort();
sort_t *new_bitvec_sort(uint64_t width);
sort_t *new_array_sort(sort_t *index, sort_t *elem);

#endif