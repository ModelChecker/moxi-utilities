#ifndef __HASH_H__
#define __HASH_H__

#include <stdint.h>

/**
 * Return the djb2 hash value of `str`
 * 
 * Adapted from: http://www.cse.yorku.ca/~oz/hash.html
*/
uint32_t djb2_hash_string(char *str);

#endif