/**
 *
 */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "io/print.h"
#include "util/char_buffer.h"


void init_char_buffer(char_buffer_t *str, size_t size)
{
    assert(size <= MAX_CHAR_BUFFER_SIZE);
    str->size = size;
    str->len = 0;
    str->data = malloc(sizeof(char) * size);
    str->data[0] = '\0';
}


void delete_char_buffer(char_buffer_t *str)
{
    free(str->data);
}


/**
 * Extends `str` by `size` chars.
 *
 * In practice, this function should be called sparingly. Otherwise, the initial
 * size of `str` is likely too low.
 */
void char_buffer_extend(char_buffer_t *str, size_t size)
{
    assert(str->size < MAX_CHAR_BUFFER_SIZE);
    size_t new_size = str->size + size;
    str->size = new_size;
    str->data = realloc(str->data, sizeof(char) * new_size);
}


void char_buffer_reset(char_buffer_t *str)
{
    str->len = 0;
    str->data[0] = '\0';
}


void char_buffer_append_char(char_buffer_t *str, char c)
{
    str->data[str->len] = c;
    str->len++;
    str->data[str->len] = '\0';
    
    // by default, extend the string by 50% if needed
    if (str->len == str->size - 1) {
        char_buffer_extend(str, str->size / 2);
    }
}


size_t char_buffer_get_length(char_buffer_t *str)
{
    return str->len;
}
