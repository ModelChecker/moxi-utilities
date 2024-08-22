/**
 * 
*/
#ifndef __STRING_PAIR_LIST_H__
#define __STRING_PAIR_LIST_H__

#include <stdint.h>


typedef struct string_list_entry string_list_entry_t;

struct string_list_entry {
    char *s1;
    string_list_entry_t *next;
};


typedef struct string_list {
    uint32_t size;
    string_list_entry_t *head;
} string_list_t;


void init_string_list(string_list_t *list);
void delete_string_list(string_list_t *list);
void string_list_append(string_list_t *list, char *s);
void string_list_remove(string_list_t *list, char *s);


#endif