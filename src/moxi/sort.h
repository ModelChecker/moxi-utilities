#ifndef __SORT_H__
#define __SORT_H__

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "util/hash.h"
#include "util/int_map.h"

/**
 * FIXME: This is a temporary solution to hash-consing sorts. Instead, we should
 * have a counter that increments each time a new sort is created and use that
 * as the hash. Then we can use a simple array to store the sorts.
 *
 * One approach could be similar to Yices, where we create a different
 * hash/equality functions and sort object for each base sort. We would no
 * longer need to store the indices for a sort since we can pass them into the
 * functions as a parameter.
 */

typedef enum {
    bool_sort,
    int_sort,
    real_sort,
    bitvec_sort,
    array_sort,
    uninterpreted_sort // User-declared sort
} base_sort_t;

// A hash-consed sort
typedef uint32_t sort_t;
extern sort_t cur_sort_id; // A counter for creating new sort IDs

/**
 * A sort is a type in the SMT-LIB2 language. It can be a base sort (BOOL, INT,
 * REAL) or a complex sort (ARRAY, BITVEC, etc.).
 *
 * `data` is a pointer to the underlying data for the sort. For base sorts, this
 * is NULL. For complex sorts, it's a pointer to the sort object. Use `base` to
 * determine the type.
 */
typedef struct sort_obj {
    base_sort_t base;
    sort_t id;
    void *data; 
} sort_obj_t;

typedef struct bv_sort_obj {
    uint64_t width;
} bv_sort_obj_t;

typedef struct array_sort_obj {
    sort_t index;
    sort_t element;
} array_sort_obj_t;

typedef struct decl_sort_obj {
    size_t num_params;
    sort_t *params;
} decl_sort_obj_t;

uint32_t sort_hash(sort_obj_t *sort_obj);
bool sort_eq(sort_obj_t *so1, sort_obj_t *so2);
const char *sort_name(sort_obj_t *sort_obj);

void init_sort_table(int_map_t *sort_table);
void delete_sort_table(int_map_t *sort_table);

/**
 * Returns the hash-consed sort object, adding it to the table if it's not
 * already in the sort table.
 */
sort_t sort_table_get(int_map_t *sort_table, sort_obj_t *sort);

sort_t get_bitvec_sort(int_map_t *sort_table, uint64_t width);
sort_t get_array_sort(int_map_t *sort_table, sort_t index, sort_t elem);

bool is_bool_sort(int_map_t *sort_table, sort_t sort);
bool is_int_sort(int_map_t *sort_table, sort_t sort);
bool is_real_sort(int_map_t *sort_table, sort_t sort);
bool is_bitvec_sort(int_map_t *sort_table, sort_t sort);
bool is_array_sort(int_map_t *sort_table, sort_t sort);
base_sort_t get_base_sort(int_map_t *sort_table, sort_t sort);

uint64_t get_bitvec_width(int_map_t *sort_table, sort_t sort);

// A rank is a list of sorts with the last element being the return sort.
typedef struct rank {
    sort_t *sorts;
    size_t len;
} rank_t;


#endif