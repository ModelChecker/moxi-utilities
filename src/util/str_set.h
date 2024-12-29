/**
 *
 */
#ifndef __STR_SET_H__
#define __STR_SET_H__

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>

#include "util/str_map.h"

typedef str_map_t str_set_t;

static void noop_delete_(void *entry) { }

void init_str_set(str_set_t *set, uint32_t size) { init_str_map(set, size, noop_delete_); }
void delete_str_set(str_set_t *set) { delete_str_map(set); }
void str_set_reset(str_set_t *set) { str_map_reset(set); }
bool in_str_set(str_set_t *set, char *string) { return str_map_find(set, string) != NULL; }
void str_set_add(str_set_t *set, char *string, size_t n) { str_map_add(set, string, n, string); }
void str_set_remove(str_set_t *set, char *string) { str_map_remove(set, string); }

#endif
