#include <stdint.h>
#include "hash.h"

/*
 * The source for Jenkins's mix and hash functions is at
 * http://www.burtleburtle.net/bob/hash/index.html. We use functions from
 * Jenkins's lookup3.c (which is Public Domain).
 */

/* Jenkins's lookup3 code */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mixx(a,b,c)                 \
{                                   \
  a -= c;  a ^= rot(c, 4);  c += b; \
  b -= a;  b ^= rot(a, 6);  a += c; \
  c -= b;  c ^= rot(b, 8);  b += a; \
  a -= c;  a ^= rot(c,16);  c += b; \
  b -= a;  b ^= rot(a,19);  a += c; \
  c -= b;  c ^= rot(b, 4);  b += a; \
}

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

/**
 * Return the djb2 hash value of null-terminated `str`. Adapted from:
 * http://www.cse.yorku.ca/~oz/hash.html
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

/*
 * Hash code for a 32 bit integer. This is based on Jenkins's lookup3 code.
 */
uint32_t jenkins_hash_uint32(uint32_t x) {
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);

  return x;
}

/*
 * Hash code for a 64 bit integer. This is based on Jenkins's lookup3 code.
 */
uint32_t jenkins_hash_uint64(uint64_t x) {
  uint32_t a, b, c;

  a = (uint32_t) x; // low order bits
  b = (uint32_t) (x >> 32); // high order bits
  c = 0xdeadbeef;
  final(a, b, c);

  return c;
}
