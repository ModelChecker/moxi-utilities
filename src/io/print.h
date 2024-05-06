/**
 * 
*/
#ifndef __ERROR_H__
#define __ERROR_H__


typedef enum module_code {
    MOD_LEX,
    MOD_PARSE,
} module_code_t;

extern const char *module_code_str[MOD_PARSE+1];

extern int debug_level;


void set_debug_level(int level);


void print_error(module_code_t code, const char *format, ...);
void print_debug(module_code_t code, int level, const char *format, ...);


#endif