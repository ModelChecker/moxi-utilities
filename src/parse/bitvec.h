#ifndef __BV_CONST_H__
#define __BV_CONST_H__

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct bv64 {
    uint32_t width;
    uint64_t value;
} bv64_t;

int bv64_from_str(char *str, size_t n, bv64_t *ans);

#endif
