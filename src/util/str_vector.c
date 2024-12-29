/**
 * 
*/
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "str_vector.h"

void init_str_vector(str_vector_t *vec, uint32_t size)
{
    if (size == 0) {
        vec->capacity = DEFAULT_STR_VECTOR_SIZE;
    } else {
        vec->capacity = size;
    }
    vec->size = 0;
    vec->data = malloc(vec->capacity * sizeof(char *)); 
    uint32_t i;
    for(i = 0; i < vec->capacity; ++i) {
        vec->data[i] = NULL;
    }
}

void delete_str_vector(str_vector_t *vec)
{
    free(vec->data);
}

void str_vector_reset(str_vector_t *vec)
{
    vec->size = 0;
    uint32_t i;
    for(i = 0; i < vec->capacity; ++i) {
        vec->data[i] = NULL;
    }
}

void str_vector_extend(str_vector_t *vec, uint32_t size)
{
    size_t new_size = vec->capacity + size;
    vec->capacity = new_size;
    vec->data = realloc(vec->data, sizeof(char *) * new_size);
}

void str_vector_append(str_vector_t *vec, char *str)
{
    if (vec->size == vec->capacity) {
        str_vector_extend(vec, vec->capacity);
    }
    vec->data[vec->size] = str;
    vec->size++;
}

