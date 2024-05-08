/**
 * 
*/
#ifndef __COMMANDS_H__
#define __COMMANDS_H__


/**
 * Each command has a `check` and `execute` function. This is similar to how Yices2 works
 * internally.
 *
 * The `check` function is a sort checker -- it takes the command and current context and checks
 * that the command is well-formed with respect to that context.
 *
 * The `execute` function modifies the context using the argument command. For example, a
 * `define-fun` command will add that function symbol to the context. A `check-system` command will
 * add a resulting `check-system-response` to the context.
*/

typedef enum moxi_command_type {
    MOX_CMD_DEFINE_SYS,
    MOX_CMD_CHECK_SYS,
    MOX_CMD_DECLARE_SORT,
    MOX_CMD_DECLARE_ENUM_SORT,
    MOX_CMD_DECLARE_CONST,
    MOX_CMD_DECLARE_FUN,
    MOX_CMD_DEFINE_SORT,
    MOX_CMD_DEFINE_CONST,
    MOX_CMD_DEFINE_FUN,
    MOX_CMD_EXIT,
    MOX_CMD_SET_LOGIC,
    MOX_CMD_ECHO
} moxi_command_type_t;


typedef struct moxi_command { 
    moxi_command_type_t type;
} moxi_command_t;


void check_define_system();
void check_check_system();
void check_declare_sort();
void check_declare_enum_sort();
void check_declare_const();
void check_declare_fun();
void check_define_sort();
void check_define_const();
void check_define_fun();
void check_exit();
void check_set_logic();
void check_echo();

void execute_define_system();
void execute_check_system();
void execute_declare_sort();
void execute_declare_enum_sort();
void execute_declare_const();
void execute_declare_fun();
void execute_define_sort();
void execute_define_const();
void execute_define_fun();
void execute_exit();
void execute_set_logic();
void execute_echo();


extern void (*moxi_check_fun[MOX_CMD_ECHO+1])();
extern void (*moxi_execute_fun[MOX_CMD_ECHO+1])();



#endif