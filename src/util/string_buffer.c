/**
 * 
*/
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "io/print.h"
#include "util/string_buffer.h"


/**
 * 
*/
void init_string_buffer(string_buffer_t *str, size_t size)
{
    assert (size <= MAX_STRING_BUFFER_SIZE);
    str->size = size;
    str->idx = 0;
    str->data = malloc(sizeof(char) * size);
    str->data[0] = '\0';
}


/**
 * 
*/
void delete_string_buffer(string_buffer_t *str)
{
    free(str->data);
}


/**
 * Extends `str` by `size` chars. 
 *
 * In practice, this function should be called sparingly. Otherwise, the initial size of `str` is
 * likely too low.
*/
void string_buffer_extend(string_buffer_t *str, size_t size)
{
    assert(str->size < MAX_STRING_BUFFER_SIZE);
    size_t new_size = str->size + size;
    str->size = new_size;
    str->data = realloc(str->data, sizeof(char) * new_size);
}


/**
 * 
*/
void string_buffer_reset(string_buffer_t *str)
{
    str->idx = 0;
    str->data[0] = '\0';
}


/**
 *
*/
void string_buffer_append_char(string_buffer_t *str, char c)
{   
    // by default, extend the string by 50% if needed
    if (str->idx == str->size-1) {
        string_buffer_extend(str, str->size/2);
    }
    str->data[str->idx] = c;
    str->idx++;
    str->data[str->idx] = '\0';
}


/**
 * 
*/
void string_buffer_append_string(string_buffer_t *str, char *s)
{
    assert(0);
}


/**
 *
*/
size_t string_buffer_get_length(string_buffer_t *str)
{
    return str->idx;
}
