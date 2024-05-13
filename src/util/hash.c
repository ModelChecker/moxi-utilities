#include <stdint.h>
#include "hash.h"

/**
 * Return the djb2 hash value of null-terminated `str`
 * 
 * Adapted from: http://www.cse.yorku.ca/~oz/hash.html
*/
uint32_t djb2_hash_string(const char *str)
{
    uint32_t hash = 5381;
    int c;

    while ((c = *str++)) {
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    }

    return hash;
}