/**
 * 
*/
#ifndef __ERROR_H__
#define __ERROR_H__


typedef enum module_code {
    PARSE
} module_code_t;


static int debug_level;


void print_error(module_code_t code, char *msg);
void print_debug(module_code_t code, int level, char *msg);
void print_log(module_code_t code, char *msg);


#endif