#ifndef __HASH_H__
#define __HASH_H__

#include <stdint.h>

uint32_t djb2_hash_string(const char *str);
uint32_t jenkins_hash_uint32(uint32_t x);
uint32_t jenkins_hash_uint64(uint64_t x);

#endif
