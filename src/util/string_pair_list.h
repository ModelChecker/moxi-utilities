/**
 * 
*/
#ifndef __STRING_PAIR_LIST_H__
#define __STRING_PAIR_LIST_H__

#include <stdint.h>


typedef struct string_pair string_pair_t;

struct string_pair {
    char *s1;
    char *s2;
    string_pair_t *next;
};


typedef struct string_pair_list {
    uint32_t size;
    string_pair_t *head;
} string_pair_list_t;


void init_string_pair_list(string_pair_list_t *list);
void delete_string_pair_list(string_pair_list_t *list);
void string_pair_list_append(string_pair_list_t *list, char *s1, char *s2);


#endif