/**
 * Definitions for a string buffer, an extendable char array.
*/
#ifndef __STRING_BUFFER_H__
#define __STRING_BUFFER_H__

#include <stddef.h>

/**
 * Maintains a printable string buffer, i.e., the last char of `data` is always `\0`.
*/
typedef struct string_buffer {
    size_t size;
    size_t idx; // index denoting end of the string (`data[idx] = '\0'`)
    char *data;
} string_buffer_t;


/**
 * 
*/
void init_string_buffer(string_buffer_t *str, size_t size);

/**
 * 
*/
void delete_string_buffer(string_buffer_t *str);

/**
 * 
*/
void string_buffer_extend(string_buffer_t *str, size_t size);

/**
 * 
*/
void string_buffer_reset(string_buffer_t *str);

/**
 *
*/
void string_buffer_append_char(string_buffer_t *str, char c);

/**
 * 
*/
void string_buffer_append_string(string_buffer_t *str, char *s);

/**
 *
*/
size_t string_buffer_get_length(string_buffer_t *str);


#endif