#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h> 

#include "moxi/sort.h"

sort_t cur_sort_id = 3; // Start at 3 since 0, 1, and 2 
                        // are reserved for bool, int, and real

sort_t new_sort_id() { return cur_sort_id++; }

uint32_t sort_hash(sort_obj_t *sort_obj)
{
    switch (sort_obj->base)
    {
    case bool_sort:
        return djb2_hash_string("Bool") ;
    case int_sort:
        return djb2_hash_string("Int") ;
    case real_sort:
        return djb2_hash_string("Real") ;
    case bitvec_sort:
    {
        bv_sort_obj_t *sort = sort_obj->data;
        return djb2_hash_string("BitVec") ^ 
                jenkins_hash_uint64(sort->width);
    }
    case array_sort:
    {
        array_sort_obj_t *sort = sort_obj->data;
        return djb2_hash_string("Array") ^ 
                jenkins_hash_uint32(sort->index) ^ 
                jenkins_hash_uint32(sort->element);
    }
    case uninterpreted_sort:
    {
        decl_sort_obj_t *sort = sort_obj->data;
        uint32_t hash = djb2_hash_string("DeclSort");
        size_t i;
        for (i = 0; i < sort->num_params; ++i) {
            hash ^= jenkins_hash_uint32(sort->params[i]);
        }
        return hash;
    }
    default:
        assert(false);
    }
}

bool sort_eq(sort_obj_t *so1, sort_obj_t *so2)
{   
    if (so1->base != so2->base) {
        return false;
    }

    switch (so1->base)
    {
    case bool_sort:
    case int_sort:
    case real_sort:
        return true;
    case bitvec_sort:
    {
        bv_sort_obj_t *bv_obj_1 = so1->data;
        bv_sort_obj_t *bv_obj_2 = so2->data;
        return bv_obj_1->width == bv_obj_2->width;
    }
    case array_sort:
    {
        array_sort_obj_t *array_obj_1 = so1->data;
        array_sort_obj_t *array_obj_2 = so2->data;
        return array_obj_1->index == array_obj_2->index && 
                array_obj_1->element == array_obj_2->element;
    }
    case uninterpreted_sort:
    {
        decl_sort_obj_t *decl_obj_1 = so1->data;
        decl_sort_obj_t *decl_obj_2 = so2->data;
        size_t i;
        for (i = 0; i < decl_obj_1->num_params; ++i) {
            if (decl_obj_1->params[i] != decl_obj_2->params[i]) {
                return false;
            }
        }
        return true;
    }
    default:
        assert(false);
    }
}

void init_sort_table(int_map_t *sort_table)
{
    init_int_map(sort_table, 0);

    // Add the bool, int, and real sorts to the table.
    sort_obj_t *bool_sort_obj = malloc(sizeof(sort_obj_t));
    bool_sort_obj->base = bool_sort;
    bool_sort_obj->id = bool_sort;
    bool_sort_obj->data = NULL;
    int_map_add(sort_table, bool_sort, bool_sort_obj);

    sort_obj_t *int_sort_obj = malloc(sizeof(sort_obj_t));
    int_sort_obj->base = int_sort;
    int_sort_obj->id = int_sort;
    int_sort_obj->data = NULL;
    int_map_add(sort_table, int_sort, int_sort_obj);

    sort_obj_t *real_sort_obj = malloc(sizeof(sort_obj_t));
    real_sort_obj->base = real_sort;
    real_sort_obj->id = real_sort;
    real_sort_obj->data = NULL;
    int_map_add(sort_table, real_sort, real_sort_obj);
}

void delete_sort_table(int_map_t *sort_table)
{
    // This will delete all the sort objects in the table as well.
    // FIXME: need to attach a delete function to the elements in int_map_t
    delete_int_map(sort_table);
}

sort_t sort_table_get(int_map_t *sort_table, sort_obj_t *sort)
{
    uint32_t hash = sort_hash(sort);

    // Find an unused hash in the sort table. We just increment the hash until
    // we find an empty spot -- should be good enough for now.
    sort_obj_t *old = int_map_find(sort_table, hash);
    while(old != NULL && !sort_eq(old, sort)) {
        hash++;
        old = int_map_find(sort_table, hash);
    }

    // If we sort is not equal to any existing sort, add it to the table.
    if (old == NULL) {
        int_map_add(sort_table, hash, sort);
    }

    return hash;
}

sort_t get_bitvec_sort(int_map_t *sort_table, uint64_t width)
{
    bv_sort_obj_t *bv_sort_obj = malloc(sizeof(bv_sort_obj_t));
    bv_sort_obj->width = width;

    sort_obj_t *sort_obj = malloc(sizeof(sort_obj_t));
    sort_obj->base = bitvec_sort;
    sort_obj->data = bv_sort_obj;

    return sort_table_get(sort_table, sort_obj);
}

sort_t get_array_sort(int_map_t *sort_table, sort_t index, sort_t elem)
{
    array_sort_obj_t *array_sort_obj = malloc(sizeof(array_sort_obj_t));
    array_sort_obj->index = index;
    array_sort_obj->element = elem;

    sort_obj_t *sort_obj = malloc(sizeof(sort_obj_t));
    sort_obj->base = array_sort;
    sort_obj->data = array_sort_obj;

    return sort_table_get(sort_table, sort_obj);
}

uint64_t get_bitvec_width(int_map_t *sort_table, sort_t sort)
{
    sort_obj_t *sort_obj = int_map_find(sort_table, sort);
    assert(sort_obj->base == bitvec_sort);
    bv_sort_obj_t *sort_data = (bv_sort_obj_t*) sort_obj->data;
    return sort_data->width;
}
