#include <assert.h>

#include "parse/bitvec.h"

/**
 * Adapted from the Yices source code. See terms/bv64_constants.c line 312.
 * 
 * Convert a string of '0's and '1's to a constant
 * - n = number of bits (n must be between 1 and 64)
 * - str must be at least n character long.
 *
 * Read the first n characters of str. All must be '0' and '1'
 * - the string is interpreted as a big-endian format: the
 *   first character is the high order bit.
 *
 * If the string format is wrong, return -1 and leave *ans unchanged.
 * Otherwise, return 0 and store the result in *ans.
 */
int bv64_from_str(char *str, size_t n, bv64_t *ans)
{
    uint64_t x;
    char *s;
    char c;

    if (n < 1 || n > 64) {
        return -1;
    }

    x = 0;
    s = str;
    do {
        n --;
        c = *s;
        s ++;
        if (c == '1') {
            x = (x << 1) | 1;
        } else if (c == '0') {
            x = (x << 1);
        } else {
            return -1;
        }
    } while (n > 0);

    ans->width = n;
    ans->value = x;

    return 0;
}
