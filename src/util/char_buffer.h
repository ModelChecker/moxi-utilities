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
    uint32_t size;
    uint32_t len; // index denoting end of the buffer (`data[idx] = '\0'`)
} char_buffer_t;

void init_char_buffer(char_buffer_t *str, uint32_t size);
void delete_char_buffer(char_buffer_t *str);
void char_buffer_extend(char_buffer_t *str, uint32_t size);
void char_buffer_reset(char_buffer_t *str);
void char_buffer_append_char(char_buffer_t *str, char c);
uint32_t char_buffer_get_length(char_buffer_t *str);


#endif
