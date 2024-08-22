#ifndef __STRING_BUFFER_H__
#define __STRING_BUFFER_H__

#include <stddef.h>

#define MAX_STRING_BUFFER_SIZE 4098

/**
 * A string buffer is an extensible array of chars. The buffer is printable,
 * i.e., the last char of `data` is always `\0`.
 *
 * - `data`: the buffer of chars
 * - `size`: the overall size of `data`
 * - `idx`: the index of the null terminator in `data` (`data[idx] = '\0'`)
 */
typedef struct string_buffer {
    char *data;
    size_t size;
    size_t len; // index denoting end of the string (`data[idx] = '\0'`)
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