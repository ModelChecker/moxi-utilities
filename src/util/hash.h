#ifndef __HASH_H__
#define __HASH_H__

#include <stdint.h>

/**
 *
*/
uint32_t djb2_hash_array(const uint32_t *val, uint32_t size);


/**
 * Return the djb2 hash value of null-terminated `str`
 * 
 * Adapted from: http://www.cse.yorku.ca/~oz/hash.html
*/
uint32_t djb2_hash_string(const char *str);


#endif