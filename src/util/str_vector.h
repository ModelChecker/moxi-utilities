#ifndef __STR_VECTOR_H__
#define __STR_VECTOR_H__

#include <stdbool.h>
#include <stdint.h>

typedef struct str_vector {
    char **data;
    uint32_t capacity;
    uint32_t size;
} str_vector_t;

#define STR_VECTOR_MAX_SIZE 65536
#define DEFAULT_STR_VECTOR_SIZE 1024

void init_str_vector(str_vector_t *vec, uint32_t size);
void delete_str_vector(str_vector_t *vec);
void str_vector_reset(str_vector_t *vec);
void str_vector_append(str_vector_t *vec, char *str);

#endif