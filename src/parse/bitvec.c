#include <assert.h>
#include <ctype.h>
#include <stdio.h>

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
int bv64_from_bin_str(char *str, uint32_t n, bv64_t *ans)
{
    int64_t x;
    uint32_t width;
    char *s;
    char c;

    if (n < 1 || n > 64) {
        return -1;
    }

    width = n;
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

    ans->width = width;
    ans->value = x;

    return 0;
}

/*
 * Adapted from the Yices source code. See terms/bv64_constants.c line 351.

 * Convert a string interpreted as an hexadecimal number to a constant.
 * - n = number of characters to read (n must be between 1 and 16)
 * - strs must be at least n character long.
 *
 * Read the first n characters of str.
 * All must be in the ranges '0' to '9' or 'a' to 'f' or 'A' to 'F'.
 * The string is read in big-endian format: first character defines
 * the four high-order bits.
 *
 * Return -1 if the format is wrong (and leave *ans unchanged).
 * Return 0 otherwise and store the result in ans.
 */
static uint32_t hextoint(char c) {
    if ('0' <= c && c <= '9') {
        return (uint32_t) (c - '0');
    } else if ('a' <= c && c <= 'f') {
        return (uint32_t) (10 + (c - 'a'));
    } else {
        // assertio should hold, this would be caught in parser
        assert('A' <= c && c <= 'F');
        return (uint32_t) (10 + (c - 'A'));
    }
}

int bv64_from_hex_str(char *str, uint32_t n, bv64_t *ans)
{
    int64_t x;
    uint32_t width;
    char *s;
    uint32_t hex;
    char c;

    if (n < 1 || n > 16) {
        return -1;
    }

    width = n * 4;
    x = 0;
    s = str;
    do {
        c = *s;
        s ++;
        if (isxdigit((int) c)) {
            hex = hextoint(c);
            if (hex < 0 || hex > 16) {
                return -1;
            }
            // set bits 4n-1 to 4n-4
            x = (x << 4) | hex;
            n --;
        } else {
            // error
            return -1;
        }
    } while (n > 0);

    ans->width = width;
    ans->value = x;

    return 0;
}
