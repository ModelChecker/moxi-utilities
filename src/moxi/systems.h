/**
 * 
*/
#ifndef __SYSTEM_H__
#define __SYSTEM_H__

#include <stdint.h>

#include "moxi/terms.h"


typedef uint32_t system_t;


typedef struct moxi_system {
    char *symbol;
    term_t init;
    term_t trans;
    term_t inv;
} moxi_system_t;


#endif