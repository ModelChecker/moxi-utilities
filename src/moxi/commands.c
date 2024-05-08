/**
 * 
*/
#include "moxi/commands.h"


void (*moxi_check_fun[MOX_CMD_ECHO+1])() = {
    check_define_system,
    check_check_system,
    check_declare_sort,
    check_declare_enum_sort,
    check_declare_const,
    check_declare_fun,
    check_define_sort,
    check_define_const,
    check_define_fun,
    check_exit,
    check_set_logic,
    check_echo
};


void (*moxi_execute_fun[MOX_CMD_ECHO+1])() = {
    execute_define_system,
    execute_check_system,
    execute_declare_sort,
    execute_declare_enum_sort,
    execute_declare_const,
    execute_declare_fun,
    execute_define_sort,
    execute_define_const,
    execute_define_fun,
    execute_exit,
    execute_set_logic,
    execute_echo
};

