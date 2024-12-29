#ifndef __PRINT_H__
#define __PRINT_H__

#include <stdio.h>
#include <inttypes.h>

#define PRINT_ERROR_LOC(filename, loc, fmt, ...)                               \
    fprintf(stderr, "%s:%" PRIu64 ":%" PRIu64 ": error: " fmt "\n", filename, loc.lineno,    \
            loc.col, ##__VA_ARGS__)

#define PRINT_ERROR(fmt, ...) fprintf(stderr, "error: " fmt "\n", ##__VA_ARGS__)

#endif
