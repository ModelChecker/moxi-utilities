#include <stdint.h>
#include "hash.h"

/**
 * Return the djb2 hash value of `str`
 * 
 * Adapted from: http://www.cse.yorku.ca/~oz/hash.html
*/
uint64_t djb2_hash_string(unsigned char *str)
{
    uint64_t hash = 5381;
    int c;

    while ((c = *str++)) {
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    }

    return hash;
}