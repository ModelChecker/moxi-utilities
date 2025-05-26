#ifndef __char_buffer_H__
#define __char_buffer_H__

#include <stddef.h>

#define MAX_CHAR_BUFFER_SIZE 4098

/**
 * A char buffer is an extensible array of chars. The buffer is printable,
 * i.e., the last char of `data` is always `\0`.
 *
 * - `data`: the buffer of chars
 * - `size`: the overall size of `data`
 * - `len`: the index of the null terminator in `data` (`data[idx] = '\0'`)
 */
typedef struct char_buffer {
    char *data;
    size_t size;
    size_t len; // index denoting end of the buffer (`data[idx] = '\0'`)
} char_buffer_t;


/**
 * Initialize a char buffer with a given size.
 */
void init_char_buffer(char_buffer_t *str, size_t size);

/**
 * Delete a char buffer.
 */
void delete_char_buffer(char_buffer_t *str);

/**
 * Extend the size of a char buffer.
 */
void char_buffer_extend(char_buffer_t *str, size_t size);

/**
 * Reset a char buffer.
 */
void char_buffer_reset(char_buffer_t *str);

/**
 * Append a char to a char buffer.
 */
void char_buffer_append_char(char_buffer_t *str, char c);

/**
 * Return the length of a char buffer.
 */
size_t char_buffer_get_length(char_buffer_t *str);


#endif
