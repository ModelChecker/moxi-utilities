#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#include "moxi/sort.h"

bool is_equal_sort(sort_t *s1, sort_t *s2)
{
    if (strcmp(s1->symbol, s2->symbol) || s1->num_indices != s2->num_indices ||
        s1->num_params != s2->num_params) {
        return false;
    }

    size_t i;
    for (i = 0; i < s1->num_indices; ++i) {
        if (s1->indices[i] != s2->indices[i]) {
            return false;
        }
    }

    for (i = 0; i < s1->num_params; ++i) {
        if (!is_equal_sort(s1->params[i], s2->params[i])) {
            return false;
        }
    }

    return true;
}

bool is_bool_sort(sort_t *sort)
{
    return !strcmp(sort->symbol, "Bool") && sort->num_indices == 0 &&
           sort->num_params == 0;
}

bool is_int_sort(sort_t *sort)
{
    return !strcmp(sort->symbol, "Int") && sort->num_indices == 0 &&
           sort->num_params == 0;
}

bool is_real_sort(sort_t *sort)
{
    return !strcmp(sort->symbol, "Real") && sort->num_indices == 0 &&
           sort->num_params == 0;
}

bool is_bitvec_sort(sort_t *sort)
{
    return !strcmp(sort->symbol, "BitVec") && sort->num_indices == 1 &&
           sort->num_params == 0;
}

bool is_array_sort(sort_t *sort)
{
    return !strcmp(sort->symbol, "Array") && sort->num_indices == 0 &&
           sort->num_params == 2;
}

uint64_t get_bitvec_width(sort_t *sort)
{
    if (!is_bitvec_sort(sort)) {
        return 0;
    }
    return sort->indices[0];
}

void init_sort(sort_t *sort, char *symbol, uint64_t indices[],
               size_t num_indices, sort_t *params[], size_t num_params)
{
    sort->symbol = symbol;
    sort->indices = malloc(sizeof(uint64_t) * num_indices);
    size_t i;
    for (i = 0; i < num_indices; ++i) {
        sort->indices[i] = indices[i];
    }
    sort->params = malloc(sizeof(sort_t *) * num_params);
    for (i = 0; i < num_params; ++i) {
        sort->params[i] = params[i];
    }
}

void delete_sort(sort_t *sort)
{
    free(sort->indices);
    size_t i;
    for (i = 0; i < sort->num_params; ++i) {
        delete_sort(sort->params[i]);
    }
    free(sort->params);
}

sort_t *new_sort(char *symbol, sort_t *params[], size_t nparams)
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    init_sort(new, symbol, NULL, 0, params, nparams);
    return new;
}

sort_t *new_bool_sort()
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    init_sort(new, "Bool", NULL, 0, NULL, 0);
    return new;
}

sort_t *new_int_sort()
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    init_sort(new, "Int", NULL, 0, NULL, 0);
    return new;
}

sort_t *new_real_sort()
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    init_sort(new, "Real", NULL, 0, NULL, 0);
    return new;
}

sort_t *new_bitvec_sort(uint64_t width)
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    init_sort(new, "BitVec", (uint64_t[]) {width}, 1, NULL, 0);
    return new;
}

sort_t *new_array_sort(sort_t *index, sort_t *elem)
{
    sort_t *new;
    new = malloc(sizeof(sort_t));
    sort_t *tmp[2] = {index, elem};
    init_sort(new, "Array", NULL, 0, tmp, 2);
    return new;
}