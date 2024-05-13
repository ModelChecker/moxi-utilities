/**
 * 
*/
#ifndef __SORTS_H__
#define __SORTS_H__

#include <stdbool.h>
#include <stdint.h>

#include "identifiers.h"


typedef struct sort sort_t;

typedef struct sort {
    identifier_t ident;
    sort_t *def; // List of arguments for parametric sorts
    uint32_t nparams;
} sort_t;


bool is_same_sort(sort_t *s1, sort_t *s2);


#endif