/**
 * 
*/
#include "moxi/identifiers.h"

#include "moxi/sorts.h"


bool is_same_sort(sort_t *s1, sort_t *s2)
{
    if (!is_same_identifier(&s1->ident, &s2->ident)) {
        return false;
    }

    if (s1->nparams != s2->nparams) {
        return false;
    }

    uint32_t i;
    for (i = 0; i < s1->nparams; ++i) {
        if (!is_same_sort(&s1->def[i], &s2->def[i])) {
            return false;
        }
    }

    return true;
}
