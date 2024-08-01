
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "parse/parser.h"

/**
 * Initializes `parser` to use `filename` as input.
 * 
 * Returns 0 on success, the result of `init_file_lexer` otherwise.
*/
int init_parser(parser_t *parser, const char *filename)
{
	int status;
    status = init_file_lexer(&parser->lex, filename);

	if (status) {
		return status;
	}

	init_int_stack(&parser->state_stack);
    parser->depth = 0;
	parser->filename = filename;
	return 0;
}

/**
 * 
*/
void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
    delete_int_stack(&parser->state_stack);
}

typedef enum parse_state {
	PS_CMD0,          PS_CMD1,          PS_CMD10,         PS_CMD11,        
	PS_CMD11a,        PS_CMD11b,        PS_CMD11c,        PS_CMD11d,       
	PS_CMD11e,        PS_CMD12,         PS_CMD12a,        PS_CMD12b,       
	PS_CMD12b0,       PS_CMD12c,        PS_CMD12c0,       PS_CMD12c1,      
	PS_CMD12c2,       PS_CMD12c3,       PS_CMD12d,        PS_CMD12d0,      
	PS_CMD2,          PS_CMD3,          PS_CMD3a,         PS_CMD3b,        
	PS_CMD4,          PS_CMD4a,         PS_CMD4b,         PS_CMD5,         
	PS_CMD5a,         PS_CMD5b,         PS_CMD6,          PS_CMD6a,        
	PS_CMD6b,         PS_CMD7,          PS_CMD7a,         PS_CMD8,         
	PS_CMD8a,         PS_CMD8b,         PS_CMD8c,         PS_CMD9,         
	PS_DONE,          PS_ERR,           PS_ERR_EXP_LP_EOF, PS_ERR_EXP_RP,   
	PS_R0,            PS_SRT0,          PS_SRT1,          PS_SRT2,         
	PS_SRT3,          PS_SRT3a,         PS_SRT3b,         PS_SRT4,         
	PS_SRT4a,         PS_SRT4b,         PS_SVL0,          PS_SVL0a,        
	PS_SVL0b,         PS_SVL1,          PS_SVL2,          PS_SVL3,         
	PS_TRM0,          PS_TRM1,          PS_TRM2,          PS_TRM3,         
	PS_TRM3a,         PS_TRM3b,         PS_TRM4,          PS_TRM4a,        
	PS_TRM4b,         PS_TRM4c,         PS_TRM4d,         PS_TRM5,         
	PS_TRM5a,         PS_TRM5b,         PS_TRM5c,         PS_TRM5d,        
	PS_TRM6,          PS_TRM7,          PS_TRM7a
} parse_state_t;

typedef enum parse_action {
	PA_ANY_WC_ERR,                       
	PA_CMD0_TOK_EOF_DONE,                
	PA_CMD0_TOK_LP_CMD1,                 
	PA_CMD0_WC_ERR_EXP_LP_EOF,           
	PA_CMD10_TOK_SYMBOL_SRT0,            
	PA_CMD11_TOK_SYMBOL_CMD11a,          
	PA_CMD11a_TOK_KW_INIT_TRM0,          
	PA_CMD11a_TOK_KW_INPUT_SVL0,         
	PA_CMD11a_TOK_KW_INV_TRM0,           
	PA_CMD11a_TOK_KW_LOCAL_SVL0,         
	PA_CMD11a_TOK_KW_OUTPUT_SVL0,        
	PA_CMD11a_TOK_KW_SUBSYS_CMD11b,      
	PA_CMD11a_TOK_KW_TRANS_TRM0,         
	PA_CMD11a_TOK_RP_DONE,               
	PA_CMD11b_TOK_LP_CMD11c,             
	PA_CMD11c_TOK_SYMBOL_CMD11d,         
	PA_CMD11d_TOK_LP_CMD11e,             
	PA_CMD11e_TOK_RP_R0,                 
	PA_CMD11e_TOK_SYMBOL_CMD11e,         
	PA_CMD12_TOK_SYMBOL_CMD12a,          
	PA_CMD12a_TOK_KW_ASSUME_CMD12b,      
	PA_CMD12a_TOK_KW_CURRENT_CMD12b,     
	PA_CMD12a_TOK_KW_FAIR_CMD12b,        
	PA_CMD12a_TOK_KW_INPUT_SVL0,         
	PA_CMD12a_TOK_KW_LOCAL_SVL0,         
	PA_CMD12a_TOK_KW_OUTPUT_SVL0,        
	PA_CMD12a_TOK_KW_QUERIES_CMD12d,     
	PA_CMD12a_TOK_KW_QUERY_CMD12c,       
	PA_CMD12a_TOK_KW_REACH_CMD12b,       
	PA_CMD12a_TOK_RP_DONE,               
	PA_CMD12b0_TOK_SYMBOL_TRM0,          
	PA_CMD12b_TOK_LP_CMD12b0,            
	PA_CMD12c0_TOK_SYMBOL_CMD12c1,       
	PA_CMD12c1_TOK_LP_CMD12c2,           
	PA_CMD12c2_TOK_SYMBOL_CMD12c3,       
	PA_CMD12c3_TOK_RP_R0,                
	PA_CMD12c3_TOK_SYMBOL_CMD12c3,       
	PA_CMD12c_TOK_LP_CMD12c0,            
	PA_CMD12d0_TOK_LP_CMD12c,            
	PA_CMD12d0_TOK_RP_DONE,              
	PA_CMD12d_TOK_LP_CMD12c,             
	PA_CMD1_TOK_RW_ASSERT_TRM0,          
	PA_CMD1_TOK_RW_CHECK_SYS_CMD12,      
	PA_CMD1_TOK_RW_DECLARE_CONST_CMD9,   
	PA_CMD1_TOK_RW_DECLARE_ENUM_SORT_CMD8,
	PA_CMD1_TOK_RW_DECLARE_FUN_CMD5,     
	PA_CMD1_TOK_RW_DECLARE_SORT_CMD7,    
	PA_CMD1_TOK_RW_DEFINE_CONST_CMD10,   
	PA_CMD1_TOK_RW_DEFINE_FUN_CMD4,      
	PA_CMD1_TOK_RW_DEFINE_SORT_CMD6,     
	PA_CMD1_TOK_RW_DEFINE_SYS_CMD11,     
	PA_CMD1_TOK_RW_ECHO_CMD2,            
	PA_CMD1_TOK_RW_EXIT_R0,              
	PA_CMD1_TOK_RW_RESET_R0,             
	PA_CMD1_TOK_RW_SET_LOGIC_CMD3,       
	PA_CMD2_TOK_STRING_R0,               
	PA_CMD3_TOK_SYMBOL_R0,               
	PA_CMD4_TOK_SYMBOL_SVL0,             
	PA_CMD5_TOK_SYMBOL_CMD3a,            
	PA_CMD5a_TOK_LP_CMD3b,               
	PA_CMD5b_TOK_RP_SRT0,                
	PA_CMD5b_WC_SRT0,                    
	PA_CMD6_TOK_SYMBOL_CMD4a,            
	PA_CMD6a_TOK_LP_CMD4b,               
	PA_CMD6b_TOK_RP_SRT0,                
	PA_CMD6b_TOK_SYMBOL_CMD4b,           
	PA_CMD7_TOK_SYMBOL_CMD5a,            
	PA_CMD7a_TOK_NUMERAL_R0,             
	PA_CMD8_TOK_SYMBOL_CMD8a,            
	PA_CMD8a_TOK_LP_CMD8b,               
	PA_CMD8b_TOK_SYMBOL_CMD8c,           
	PA_CMD8c_TOK_RP_R0,                  
	PA_CMD8c_TOK_SYMBOL_CMD8c,           
	PA_CMD9_TOK_SYMBOL_SRT0,             
	PA_ERR_EXP_LP_EOF_WC_ERR,            
	PA_ERR_EXP_RP_WC_ERR,                
	PA_R0_TOK_RP_DONE,                   
	PA_R0_WC_ERR_EXP_RP,                 
	PA_SRT0_TOK_LP_SRT1,                 
	PA_SRT0_TOK_SYMBOL_DONE,             
	PA_SRT1_TOK_LP_SRT4,                 
	PA_SRT1_TOK_RW_UNDERSCORE_SRT3,      
	PA_SRT1_TOK_SYMBOL_SRT0,             
	PA_SRT2_TOK_RP_DONE,                 
	PA_SRT2_WC_SRT0,                     
	PA_SRT3_TOK_SYMBOL_SRT3a,            
	PA_SRT3a_TOK_NUMERAL_SRT3b,          
	PA_SRT3b_TOK_NUMERAL_SRT3b,          
	PA_SRT3b_TOK_RP_DONE,                
	PA_SRT4_TOK_SYMBOL_SRT4a,            
	PA_SRT4a_TOK_NUMERAL_SRT4b,          
	PA_SRT4b_TOK_NUMERAL_SRT4b,          
	PA_SRT4b_TOK_RP_SRT0,                
	PA_SVL0_TOK_LP_SVL1,                 
	PA_SVL0a_TOK_LP_SVL0b,               
	PA_SVL0b_TOK_LP_SVL2,                
	PA_SVL1_TOK_LP_SVL2,                 
	PA_SVL1_TOK_RP_DONE,                 
	PA_SVL2_TOK_SYMBOL_SRT0,             
	PA_SVL3_TOK_RP_SVL1,                 
	PA_TRM0_TOK_BINARY_DONE,             
	PA_TRM0_TOK_DECIMAL_DONE,            
	PA_TRM0_TOK_HEX_DONE,                
	PA_TRM0_TOK_LP_TRM1,                 
	PA_TRM0_TOK_NUMERAL_DONE,            
	PA_TRM0_TOK_STRING_DONE,             
	PA_TRM0_TOK_SYMBOL_DONE,             
	PA_TRM1_TOK_LP_TRM7,                 
	PA_TRM1_TOK_RW_AS_TRM4,              
	PA_TRM1_TOK_RW_EXISTS_TRM6,          
	PA_TRM1_TOK_RW_FORALL_TRM6,          
	PA_TRM1_TOK_RW_LET_TRM5,             
	PA_TRM1_TOK_RW_UNDERSCORE_TRM3,      
	PA_TRM1_TOK_SYMBOL_TRM0,             
	PA_TRM2_TOK_RP_DONE,                 
	PA_TRM2_WC_TRM0,                     
	PA_TRM3_TOK_SYMBOL_TRM3a,            
	PA_TRM3a_TOK_NUMERAL_TRM3b,          
	PA_TRM3b_TOK_NUMERAL_TRM3b,          
	PA_TRM3b_TOK_RP_DONE,                
	PA_TRM4_TOK_LP_TRM4a,                
	PA_TRM4_TOK_SYMBOL_SRT0,             
	PA_TRM4a_TOK_RW_UNDERSCORE_TRM4b,    
	PA_TRM4b_TOK_SYMBOL_TRM4c,           
	PA_TRM4c_TOK_NUMERAL_TRM4d,          
	PA_TRM4d_TOK_NUMERAL_TRM4d,          
	PA_TRM4d_TOK_RP_SRT0,                
	PA_TRM5_TOK_LP_TRM5a,                
	PA_TRM5a_TOK_LP_TRM5b,               
	PA_TRM5b_TOK_SYMBOL_TRM0,            
	PA_TRM5c_TOK_RP_TRM5d,               
	PA_TRM5d_TOK_LP_TRM5b,               
	PA_TRM5d_TOK_RP_TRM0,                
	PA_TRM6_TOK_LP_SVL0a,                
	PA_TRM7_TOK_RW_AS_TRM4,              
	PA_TRM7_TOK_RW_UNDERSCORE_TRM3,      
	PA_TRM7a_TOK_RP_DONE,                
	PA_TRM7a_WC_TRM0
} parse_action_t;

const int def[79] = {
	PA_CMD0_WC_ERR_EXP_LP_EOF, PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_CMD5b_WC_SRT0,        
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ERR_EXP_LP_EOF_WC_ERR, PA_ERR_EXP_RP_WC_ERR,    
	PA_R0_WC_ERR_EXP_RP,      PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_SRT2_WC_SRT0,         
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_TRM2_WC_TRM0,          PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_ANY_WC_ERR,            PA_ANY_WC_ERR,           
	PA_TRM7a_WC_TRM0
};

const int base[79] = {
	0,  0,  0,  1,  0,  2,  2,  3,  3,  4,  38, 5,  5,  6,  6, 
	7,  7,  8,  8,  10, 6,  9,  0,  0,  10, 0,  0,  11, 13, 13,
	12, 15, 15, 13, 15, 14, 40, 16, 40, 17, 0,  0,  0,  0,  41,
	43, 64, 43, 19, 43, 65, 22, 67, 72, 76, 83, 84, 87, 39, 89,
	91, 92, 97, 53, 98, 100, 104, 94, 65, 110, 112, 115, 116, 71, 117,
	119, 121, 111, 122
};

const int check[179] = {
	0, 0, 4, 5, 7, 8, 11, 13, 15, 18, 17, 19, 19, 20, 28, 29, 31, 32, 34,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4,
	4, 4, 10, 36, 38, 44, 45, 47, 49, 2, 3, 6, 8, 9, 12, 14, 16, 17, 21,
	24, 27, 30, 33, 35, 32, 37, 39, 46, 48, 50, 50, 51, 52, 10, 10, 10, 53, 53,
	46, 54, 10, 10, 10, 10, 10, 10, 55, 56, 58, 38, 57, 57, 45, 59, 60, 61, 60,
	60, 60, 60, 60, 62, 63, 64, 65, 65, 61, 66, 67, 61, 61, 61, 61, 46, 68, 69,
	70, 70, 71, 72, 73, 74, 75, 75, 76, 77, 78, 79, 77, 79, 79, 79, 79, 79, 79,
	79, 79, 79, 79, 79, 60, 61, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 66,
	79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
	79, 79, 79, 79, 79, 79, 79, 79
};

const int value[179] = {
	1,  2,  13, 14, 16, 17, 31, 37, 33, 40, 35, 38, 39, 55, 59,
	60, 63, 64, 67, 50, 42, 46, 44, 43, 45, 49, 47, 48, 52, 54,
	51, 53, 41, 7,  10, 9,  6,  12, 8,  11, 29, 69, 71, 76, 78,
	83, 86, 4,  5,  15, 18, 19, 30, 32, 34, 36, 56, 57, 58, 62,
	66, 68, 65, 70, 73, 80, 85, 88, 87, 89, 90, 23, 25, 24, 92,
	91, 81, 93, 20, 28, 22, 21, 27, 26, 94, 95, 98, 72, 96, 97,
	79, 99, 103, 107, 104, 101, 100, 102, 105, 114, 116, 117, 119, 118, 112,
	120, 122, 108, 111, 109, 110, 82, 123, 124, 126, 125, 127, 128, 129, 130,
	131, 132, 133, 135, 136, 41, 134, 41, 41, 41, 41, 41, 41, 41, 41,
	41, 41, 41, 106, 113, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41,
	41, 121, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41,
	41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41
};


parse_action_t get_action(parse_state_t state, token_type_t token) 
{
    int i;
    i = base[state] + token;
    if (check[i] == state) {
        return value[i];
    } else {
        return def[state];
    }
}

int parse_moxi(parser_t *parser) 
{
    lexer_t *lex;
    const char *filename;
    token_type_t token;
    int_stack_t *state_stack;
    parse_state_t state;
    parse_action_t action;
    uint64_t lineno;
    uint64_t col;

    filename = parser->filename;
    lex = &parser->lex;
    state_stack = &parser->state_stack;
    state = PS_CMD0;

consume:
    if (state ==PS_DONE && state_stack->top == 0) {
		//fprintf(stderr, "state=PS_DONE and stack is empty, exiting\n");
		return 0;
	}

    lexer_next_token(lex);
	token = lex->tok_type;
    lineno = lex->lineno;
    col = lex->col;

skip:
    if (state == PS_ERR) {
        print_error_with_loc(filename, MOD_PARSE, lineno, col, "syntax error");
        return 1;
    } 
    
    if (state == PS_DONE) {
        if (state_stack->top == 0) {
            //fprintf(stderr, "state=PS_DONE and stack is empty, exiting\n");
            return 0;
        }
        state = int_stack_pop(state_stack);
        //fprintf(stderr, "popping %d\n", state);
    }

    action = get_action(state, token);
    //fprintf(stderr, "state: %d, token: '%s' (%d), action: %d\n", state, token_type_str[token], token, action);
    switch(action) {
		case PA_ERR_EXP_RP_WC_ERR:
			state = PS_ERR;
			goto skip;

 		case PA_ERR_EXP_LP_EOF_WC_ERR:
			state = PS_ERR;
			goto skip;

 		case PA_R0_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_R0_WC_ERR_EXP_RP:
			state = PS_ERR_EXP_RP;
			goto consume;

 		case PA_CMD0_TOK_LP_CMD1:
			state = PS_CMD1;
			goto consume;

 		case PA_CMD0_TOK_EOF_DONE:
			state = PS_DONE;
			goto skip;

 		case PA_CMD0_WC_ERR_EXP_LP_EOF:
			state = PS_ERR_EXP_LP_EOF;
			goto skip;

 		case PA_CMD1_TOK_RW_EXIT_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD1_TOK_RW_RESET_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD1_TOK_RW_ASSERT_TRM0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD1_TOK_RW_ECHO_CMD2:
			state = PS_CMD2;
			goto consume;

 		case PA_CMD1_TOK_RW_SET_LOGIC_CMD3:
			state = PS_CMD3;
			goto consume;

 		case PA_CMD1_TOK_RW_DEFINE_FUN_CMD4:
			state = PS_CMD4;
			goto consume;

 		case PA_CMD1_TOK_RW_DECLARE_FUN_CMD5:
			state = PS_CMD5;
			goto consume;

 		case PA_CMD1_TOK_RW_DEFINE_SORT_CMD6:
			state = PS_CMD6;
			goto consume;

 		case PA_CMD1_TOK_RW_DECLARE_SORT_CMD7:
			state = PS_CMD7;
			goto consume;

 		case PA_CMD1_TOK_RW_DECLARE_ENUM_SORT_CMD8:
			state = PS_CMD8;
			goto consume;

 		case PA_CMD1_TOK_RW_DECLARE_CONST_CMD9:
			state = PS_CMD9;
			goto consume;

 		case PA_CMD1_TOK_RW_DEFINE_CONST_CMD10:
			state = PS_CMD10;
			goto consume;

 		case PA_CMD1_TOK_RW_DEFINE_SYS_CMD11:
			state = PS_CMD11;
			goto consume;

 		case PA_CMD1_TOK_RW_CHECK_SYS_CMD12:
			state = PS_CMD12;
			goto consume;

 		case PA_CMD2_TOK_STRING_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD3_TOK_SYMBOL_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD4_TOK_SYMBOL_SVL0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(state_stack, PS_TRM0);
			//fprintf(stderr, "pushing %d\n", PS_TRM0);
			int_stack_push(state_stack, PS_SRT0);
			//fprintf(stderr, "pushing %d\n", PS_SRT0);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD5_TOK_SYMBOL_CMD3a:
			state = PS_CMD3a;
			goto consume;

 		case PA_CMD5a_TOK_LP_CMD3b:
			state = PS_CMD3b;
			goto consume;

 		case PA_CMD5b_TOK_RP_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD5b_WC_SRT0:
			int_stack_push(state_stack, PS_CMD3b);
			//fprintf(stderr, "pushing %d\n", PS_CMD3b);
			state = PS_SRT0;
			goto skip;

 		case PA_CMD6_TOK_SYMBOL_CMD4a:
			state = PS_CMD4a;
			goto consume;

 		case PA_CMD6a_TOK_LP_CMD4b:
			state = PS_CMD4b;
			goto consume;

 		case PA_CMD6b_TOK_RP_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD6b_TOK_SYMBOL_CMD4b:
			state = PS_CMD4b;
			goto consume;

 		case PA_CMD7_TOK_SYMBOL_CMD5a:
			state = PS_CMD5a;
			goto consume;

 		case PA_CMD7a_TOK_NUMERAL_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD8_TOK_SYMBOL_CMD8a:
			state = PS_CMD8a;
			goto consume;

 		case PA_CMD8a_TOK_LP_CMD8b:
			state = PS_CMD8b;
			goto consume;

 		case PA_CMD8b_TOK_SYMBOL_CMD8c:
			state = PS_CMD8c;
			goto consume;

 		case PA_CMD8c_TOK_SYMBOL_CMD8c:
			state = PS_CMD8c;
			goto consume;

 		case PA_CMD8c_TOK_RP_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD9_TOK_SYMBOL_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD10_TOK_SYMBOL_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(state_stack, PS_TRM0);
			//fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD11_TOK_SYMBOL_CMD11a:
			state = PS_CMD11a;
			goto consume;

 		case PA_CMD11a_TOK_KW_INPUT_SVL0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_OUTPUT_SVL0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_LOCAL_SVL0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_INIT_TRM0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_TRANS_TRM0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_INV_TRM0:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_SUBSYS_CMD11b:
			int_stack_push(state_stack, PS_CMD11a);
			//fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_CMD11b;
			goto consume;

 		case PA_CMD11a_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_CMD11b_TOK_LP_CMD11c:
			state = PS_CMD11c;
			goto consume;

 		case PA_CMD11c_TOK_SYMBOL_CMD11d:
			state = PS_CMD11d;
			goto consume;

 		case PA_CMD11d_TOK_LP_CMD11e:
			state = PS_CMD11e;
			goto consume;

 		case PA_CMD11e_TOK_SYMBOL_CMD11e:
			state = PS_CMD11e;
			goto consume;

 		case PA_CMD11e_TOK_RP_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD12_TOK_SYMBOL_CMD12a:
			state = PS_CMD12a;
			goto consume;

 		case PA_CMD12a_TOK_KW_INPUT_SVL0:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12a_TOK_KW_OUTPUT_SVL0:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12a_TOK_KW_LOCAL_SVL0:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12a_TOK_KW_ASSUME_CMD12b:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12b;
			goto consume;

 		case PA_CMD12a_TOK_KW_CURRENT_CMD12b:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12b;
			goto consume;

 		case PA_CMD12a_TOK_KW_REACH_CMD12b:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12b;
			goto consume;

 		case PA_CMD12a_TOK_KW_FAIR_CMD12b:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12b;
			goto consume;

 		case PA_CMD12a_TOK_KW_QUERY_CMD12c:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12c;
			goto consume;

 		case PA_CMD12a_TOK_KW_QUERIES_CMD12d:
			int_stack_push(state_stack, PS_CMD12a);
			//fprintf(stderr, "pushing %d\n", PS_CMD12a);
			state = PS_CMD12d;
			goto consume;

 		case PA_CMD12a_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_CMD12b_TOK_LP_CMD12b0:
			state = PS_CMD12b0;
			goto consume;

 		case PA_CMD12b0_TOK_SYMBOL_TRM0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD12c_TOK_LP_CMD12c0:
			state = PS_CMD12c0;
			goto consume;

 		case PA_CMD12c0_TOK_SYMBOL_CMD12c1:
			state = PS_CMD12c1;
			goto consume;

 		case PA_CMD12c1_TOK_LP_CMD12c2:
			state = PS_CMD12c2;
			goto consume;

 		case PA_CMD12c2_TOK_SYMBOL_CMD12c3:
			state = PS_CMD12c3;
			goto consume;

 		case PA_CMD12c3_TOK_SYMBOL_CMD12c3:
			state = PS_CMD12c3;
			goto consume;

 		case PA_CMD12c3_TOK_RP_R0:
			state = PS_R0;
			goto consume;

 		case PA_CMD12d_TOK_LP_CMD12c:
			int_stack_push(state_stack, PS_CMD12d0);
			//fprintf(stderr, "pushing %d\n", PS_CMD12d0);
			state = PS_CMD12c;
			goto consume;

 		case PA_CMD12d0_TOK_LP_CMD12c:
			int_stack_push(state_stack, PS_CMD12d0);
			//fprintf(stderr, "pushing %d\n", PS_CMD12d0);
			state = PS_CMD12c;
			goto skip;

 		case PA_CMD12d0_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_NUMERAL_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_DECIMAL_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_HEX_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_BINARY_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_STRING_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_SYMBOL_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM0_TOK_LP_TRM1:
			state = PS_TRM1;
			goto consume;

 		case PA_TRM1_TOK_SYMBOL_TRM0:
			int_stack_push(state_stack, PS_TRM2);
			//fprintf(stderr, "pushing %d\n", PS_TRM2);
			state = PS_TRM0;
			goto consume;

 		case PA_TRM1_TOK_RW_UNDERSCORE_TRM3:
			state = PS_TRM3;
			goto consume;

 		case PA_TRM1_TOK_RW_AS_TRM4:
			state = PS_TRM4;
			goto consume;

 		case PA_TRM1_TOK_RW_LET_TRM5:
			state = PS_TRM5;
			goto consume;

 		case PA_TRM1_TOK_RW_FORALL_TRM6:
			state = PS_TRM6;
			goto consume;

 		case PA_TRM1_TOK_RW_EXISTS_TRM6:
			state = PS_TRM6;
			goto consume;

 		case PA_TRM1_TOK_LP_TRM7:
			state = PS_TRM7;
			goto consume;

 		case PA_TRM2_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM2_WC_TRM0:
			int_stack_push(state_stack, PS_TRM2);
			//fprintf(stderr, "pushing %d\n", PS_TRM2);
			state = PS_TRM0;
			goto skip;

 		case PA_TRM3_TOK_SYMBOL_TRM3a:
			state = PS_TRM3a;
			goto consume;

 		case PA_TRM3a_TOK_NUMERAL_TRM3b:
			state = PS_TRM3b;
			goto consume;

 		case PA_TRM3b_TOK_NUMERAL_TRM3b:
			state = PS_TRM3b;
			goto consume;

 		case PA_TRM3b_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM4_TOK_SYMBOL_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_TRM4_TOK_LP_TRM4a:
			state = PS_TRM4a;
			goto consume;

 		case PA_TRM4a_TOK_RW_UNDERSCORE_TRM4b:
			state = PS_TRM4b;
			goto consume;

 		case PA_TRM4b_TOK_SYMBOL_TRM4c:
			state = PS_TRM4c;
			goto consume;

 		case PA_TRM4c_TOK_NUMERAL_TRM4d:
			state = PS_TRM4d;
			goto consume;

 		case PA_TRM4d_TOK_NUMERAL_TRM4d:
			state = PS_TRM4d;
			goto consume;

 		case PA_TRM4d_TOK_RP_SRT0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_TRM5_TOK_LP_TRM5a:
			state = PS_TRM5a;
			goto consume;

 		case PA_TRM5a_TOK_LP_TRM5b:
			state = PS_TRM5b;
			goto consume;

 		case PA_TRM5b_TOK_SYMBOL_TRM0:
			int_stack_push(state_stack, PS_TRM5c);
			//fprintf(stderr, "pushing %d\n", PS_TRM5c);
			state = PS_TRM0;
			goto consume;

 		case PA_TRM5c_TOK_RP_TRM5d:
			state = PS_TRM5d;
			goto consume;

 		case PA_TRM5d_TOK_LP_TRM5b:
			state = PS_TRM5b;
			goto consume;

 		case PA_TRM5d_TOK_RP_TRM0:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_TRM0;
			goto consume;

 		case PA_TRM6_TOK_LP_SVL0a:
			int_stack_push(state_stack, PS_R0);
			//fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(state_stack, PS_TRM0);
			//fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_SVL0a;
			goto skip;

 		case PA_TRM7_TOK_RW_UNDERSCORE_TRM3:
			int_stack_push(state_stack, PS_TRM7a);
			//fprintf(stderr, "pushing %d\n", PS_TRM7a);
			int_stack_push(state_stack, PS_TRM0);
			//fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_TRM3;
			goto consume;

 		case PA_TRM7_TOK_RW_AS_TRM4:
			int_stack_push(state_stack, PS_TRM7a);
			//fprintf(stderr, "pushing %d\n", PS_TRM7a);
			int_stack_push(state_stack, PS_TRM0);
			//fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_TRM4;
			goto consume;

 		case PA_TRM7a_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_TRM7a_WC_TRM0:
			state = PS_TRM0;
			goto skip;

 		case PA_SVL0_TOK_LP_SVL1:
			state = PS_SVL1;
			goto consume;

 		case PA_SVL0a_TOK_LP_SVL0b:
			state = PS_SVL0b;
			goto consume;

 		case PA_SVL0b_TOK_LP_SVL2:
			state = PS_SVL2;
			goto consume;

 		case PA_SVL1_TOK_LP_SVL2:
			state = PS_SVL2;
			goto consume;

 		case PA_SVL1_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_SVL2_TOK_SYMBOL_SRT0:
			int_stack_push(state_stack, PS_SVL3);
			//fprintf(stderr, "pushing %d\n", PS_SVL3);
			state = PS_SRT0;
			goto consume;

 		case PA_SVL3_TOK_RP_SVL1:
			state = PS_SVL1;
			goto consume;

 		case PA_SRT0_TOK_SYMBOL_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_SRT0_TOK_LP_SRT1:
			state = PS_SRT1;
			goto consume;

 		case PA_SRT1_TOK_SYMBOL_SRT0:
			int_stack_push(state_stack, PS_SRT2);
			//fprintf(stderr, "pushing %d\n", PS_SRT2);
			state = PS_SRT0;
			goto consume;

 		case PA_SRT1_TOK_RW_UNDERSCORE_SRT3:
			state = PS_SRT3;
			goto consume;

 		case PA_SRT1_TOK_LP_SRT4:
			state = PS_SRT4;
			goto consume;

 		case PA_SRT2_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_SRT2_WC_SRT0:
			int_stack_push(state_stack, PS_SRT2);
			//fprintf(stderr, "pushing %d\n", PS_SRT2);
			state = PS_SRT0;
			goto skip;

 		case PA_SRT3_TOK_SYMBOL_SRT3a:
			state = PS_SRT3a;
			goto consume;

 		case PA_SRT3a_TOK_NUMERAL_SRT3b:
			state = PS_SRT3b;
			goto consume;

 		case PA_SRT3b_TOK_NUMERAL_SRT3b:
			state = PS_SRT3b;
			goto consume;

 		case PA_SRT3b_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_SRT4_TOK_SYMBOL_SRT4a:
			state = PS_SRT4a;
			goto consume;

 		case PA_SRT4a_TOK_NUMERAL_SRT4b:
			state = PS_SRT4b;
			goto consume;

 		case PA_SRT4b_TOK_NUMERAL_SRT4b:
			state = PS_SRT4b;
			goto consume;

 		case PA_SRT4b_TOK_RP_SRT0:
			int_stack_push(state_stack, PS_SRT2);
			//fprintf(stderr, "pushing %d\n", PS_SRT2);
			state = PS_SRT0;
			goto consume;

 		case PA_ANY_WC_ERR:
			state = PS_ERR;
			goto skip;

	}

	return 1;
}

