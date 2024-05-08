/**
 * 
*/
#ifndef __SYSTEM_H__
#define __SYSTEM_H__

#include "moxi/terms.h"


typedef struct moxi_system {
    term_t init;
    term_t trans;
    term_t inv;
} moxi_system_t;


#endif