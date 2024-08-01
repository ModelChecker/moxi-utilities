
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "parse/parse_error.h"
#include "parse/parser.h"

/**
 * 
*/
void init_parser(parser_t *parser, const char *filename)
{
    init_lexer(&parser->lex, filename);
	init_int_stack(&parser->pstack);
    parser->depth = 0;
}

/**
 * 
*/
void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
    delete_int_stack(&parser->pstack);
}

typedef enum parse_state {
	PS_CMD0,          PS_CMD1,          PS_CMD10,         PS_CMD11,        
	PS_CMD11a,        PS_CMD11b,        PS_CMD11c,        PS_CMD11d,       
	PS_CMD11e,        PS_CMD12,         PS_CMD12a,        PS_CMD12a0,      
	PS_CMD12b,        PS_CMD12b0,       PS_CMD12b1,       PS_CMD12b2,      
	PS_CMD12b3,       PS_CMD12c,        PS_CMD2,          PS_CMD3,         
	PS_CMD3a,         PS_CMD3b,         PS_CMD4,          PS_CMD4a,        
	PS_CMD4b,         PS_CMD5,          PS_CMD5a,         PS_CMD5b,        
	PS_CMD6,          PS_CMD6a,         PS_CMD6b,         PS_CMD7,         
	PS_CMD7a,         PS_CMD8,          PS_CMD8a,         PS_CMD8b,        
	PS_CMD8c,         PS_CMD9,          PS_DONE,          PS_ERR,          
	PS_ERR_EXP_LP_EOF, PS_ERR_EXP_RP,    PS_R0,            PS_SRT0,         
	PS_SRT1,          PS_SRT2,          PS_SRT3,          PS_SRT3a,        
	PS_SRT3b,         PS_SRT4,          PS_SRT4a,         PS_SRT4b,        
	PS_SVL0,          PS_SVL0a,         PS_SVL0b,         PS_SVL1,         
	PS_SVL2,          PS_SVL3,          PS_TRM0,          PS_TRM1,         
	PS_TRM2,          PS_TRM3,          PS_TRM3a,         PS_TRM3b,        
	PS_TRM4,          PS_TRM4a,         PS_TRM4b,         PS_TRM4c,        
	PS_TRM4d,         PS_TRM5,          PS_TRM5a,         PS_TRM5b,        
	PS_TRM5c,         PS_TRM5d,         PS_TRM6,          PS_TRM7,         
	PS_TRM7a
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
	PA_CMD12_TOK_KW_ASSUME_CMD12a,       
	PA_CMD12_TOK_KW_CURRENT_CMD12a,      
	PA_CMD12_TOK_KW_FAIR_CMD12a,         
	PA_CMD12_TOK_KW_INPUT_SVL0,          
	PA_CMD12_TOK_KW_LOCAL_SVL0,          
	PA_CMD12_TOK_KW_OUTPUT_SVL0,         
	PA_CMD12_TOK_KW_QUERIES_CMD12c,      
	PA_CMD12_TOK_KW_QUERY_CMD12b,        
	PA_CMD12_TOK_KW_REACH_CMD12a,        
	PA_CMD12_TOK_RP_DONE,                
	PA_CMD12a0_TOK_SYMBOL_TRM0,          
	PA_CMD12a_TOK_LP_CMD12a0,            
	PA_CMD12b0_TOK_SYMBOL_CMD12b1,       
	PA_CMD12b1_TOK_LP_CMD12b2,           
	PA_CMD12b2_TOK_SYMBOL_CMD12b3,       
	PA_CMD12b3_TOK_RP_R0,                
	PA_CMD12b3_TOK_SYMBOL_CMD12b3,       
	PA_CMD12b_TOK_LP_CMD12b0,            
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

const int def[77] = {
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

const int base[77] = {
	0,  0,  0,  1,  0,  2,  2,  3,  3,  11, 5,  10, 6,  11, 7, 
	12, 13, 0,  2,  14, 0,  0,  15, 0,  0,  16, 9,  9,  17, 11,
	38, 18, 11, 19, 15, 20, 39, 21, 0,  0,  0,  0,  15, 41, 68,
	16, 23, 40, 69, 26, 71, 73, 76, 77, 78, 80, 36, 82, 86, 93,
	93, 49, 94, 96, 99, 89, 55, 100, 104, 103, 111, 66, 112, 115, 117,
	107, 118
};

const int check[175] = {
	0, 0, 4, 5, 7, 8, 10, 12, 14, 18, 26, 27, 29, 9, 32, 16, 34, 42, 45,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4,
	4, 4, 30, 36, 43, 47, 9, 9, 9, 2, 3, 6, 8, 9, 9, 9, 9, 9, 9,
	11, 13, 15, 16, 19, 22, 25, 28, 31, 33, 35, 37, 44, 46, 48, 48, 49, 50, 51,
	51, 52, 53, 54, 44, 55, 55, 56, 57, 30, 36, 58, 43, 58, 58, 58, 58, 58, 59,
	60, 61, 62, 63, 63, 64, 65, 66, 67, 69, 59, 68, 68, 59, 59, 59, 59, 70, 71,
	72, 44, 73, 73, 74, 75, 76, 77, 75, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77,
	58, 77, 77, 77, 77, 77, 77, 59, 77, 77, 77, 77, 77, 64, 77, 77, 77, 77, 77,
	77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77, 77,
	77, 77, 77, 77
};

const int value[175] = {
	1,  2,  13, 14, 16, 17, 30, 36, 32, 51, 55, 56, 59, 28, 63,
	34, 65, 72, 79, 46, 38, 42, 40, 39, 41, 45, 43, 44, 48, 50,
	47, 49, 37, 7,  10, 9,  6,  12, 8,  11, 60, 67, 74, 82, 22,
	24, 23, 4,  5,  15, 18, 19, 27, 21, 20, 26, 25, 29, 31, 33,
	35, 52, 53, 54, 58, 62, 64, 66, 69, 76, 81, 84, 83, 85, 86,
	88, 87, 89, 90, 91, 77, 92, 93, 94, 95, 61, 68, 99, 75, 100,
	97, 96, 98, 101, 103, 110, 112, 113, 115, 114, 116, 118, 119, 120, 123,
	108, 122, 121, 104, 107, 105, 106, 124, 125, 126, 78, 127, 128, 129, 131,
	132, 39, 130, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 102, 39,
	39, 39, 39, 39, 39, 109, 39, 39, 39, 39, 39, 117, 39, 39, 39,
	39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39,
	39, 39, 39, 39, 39, 39, 39, 39, 39, 39
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
    //loc_t loc;
    token_type_t token;
    int_stack_t *pstack;
    parse_state_t state;
    parse_action_t action;

    lex = &parser->lex;
    pstack = &parser->pstack;
    state = PS_CMD0;

consume:
    if (state == PS_DONE && pstack->top == 0) {
		fprintf(stderr, "state=PS_DONE and stack is empty, exiting\n");
		return 0;
	}

    lexer_next_token(lex);
	token = lex->tok_type;
    //loc = lex->loc;

skip:
    if (state == PS_ERR) {
        fprintf(stderr, "syntax error\n");
        return 1;
    } 
    
    if (state == PS_DONE) {
        if (pstack->top == 0) {
            fprintf(stderr, "state=PS_DONE and stack is empty, exiting\n");
            return 0;
        }
        state = int_stack_pop(pstack);
        fprintf(stderr, "popping %d\n", state);
    }

    action = get_action(state, token);
    fprintf(stderr, "state: %d, token: '%s' (%d), action: %d\n", state, token_type_str[token], token, action);
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
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
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
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(pstack, PS_TRM0);
			fprintf(stderr, "pushing %d\n", PS_TRM0);
			int_stack_push(pstack, PS_SRT0);
			fprintf(stderr, "pushing %d\n", PS_SRT0);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD5_TOK_SYMBOL_CMD3a:
			state = PS_CMD3a;
			goto consume;

 		case PA_CMD5a_TOK_LP_CMD3b:
			state = PS_CMD3b;
			goto consume;

 		case PA_CMD5b_TOK_RP_SRT0:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD5b_WC_SRT0:
			int_stack_push(pstack, PS_CMD3b);
			fprintf(stderr, "pushing %d\n", PS_CMD3b);
			state = PS_SRT0;
			goto skip;

 		case PA_CMD6_TOK_SYMBOL_CMD4a:
			state = PS_CMD4a;
			goto consume;

 		case PA_CMD6a_TOK_LP_CMD4b:
			state = PS_CMD4b;
			goto consume;

 		case PA_CMD6b_TOK_RP_SRT0:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
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
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD10_TOK_SYMBOL_SRT0:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(pstack, PS_TRM0);
			fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_SRT0;
			goto consume;

 		case PA_CMD11_TOK_SYMBOL_CMD11a:
			state = PS_CMD11a;
			goto consume;

 		case PA_CMD11a_TOK_KW_INPUT_SVL0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_OUTPUT_SVL0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_LOCAL_SVL0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD11a_TOK_KW_INIT_TRM0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_TRANS_TRM0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_INV_TRM0:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD11a_TOK_KW_SUBSYS_CMD11b:
			int_stack_push(pstack, PS_CMD11a);
			fprintf(stderr, "pushing %d\n", PS_CMD11a);
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

 		case PA_CMD12_TOK_KW_INPUT_SVL0:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12_TOK_KW_OUTPUT_SVL0:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12_TOK_KW_LOCAL_SVL0:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_SVL0;
			goto consume;

 		case PA_CMD12_TOK_KW_ASSUME_CMD12a:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12a;
			goto consume;

 		case PA_CMD12_TOK_KW_CURRENT_CMD12a:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12a;
			goto consume;

 		case PA_CMD12_TOK_KW_REACH_CMD12a:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12a;
			goto consume;

 		case PA_CMD12_TOK_KW_FAIR_CMD12a:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12a;
			goto consume;

 		case PA_CMD12_TOK_KW_QUERY_CMD12b:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12b;
			goto consume;

 		case PA_CMD12_TOK_KW_QUERIES_CMD12c:
			int_stack_push(pstack, PS_CMD12);
			fprintf(stderr, "pushing %d\n", PS_CMD12);
			state = PS_CMD12c;
			goto consume;

 		case PA_CMD12_TOK_RP_DONE:
			state = PS_DONE;
			goto consume;

 		case PA_CMD12a_TOK_LP_CMD12a0:
			state = PS_CMD12a0;
			goto consume;

 		case PA_CMD12a0_TOK_SYMBOL_TRM0:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_TRM0;
			goto consume;

 		case PA_CMD12b_TOK_LP_CMD12b0:
			state = PS_CMD12b0;
			goto consume;

 		case PA_CMD12b0_TOK_SYMBOL_CMD12b1:
			state = PS_CMD12b1;
			goto consume;

 		case PA_CMD12b1_TOK_LP_CMD12b2:
			state = PS_CMD12b2;
			goto consume;

 		case PA_CMD12b2_TOK_SYMBOL_CMD12b3:
			state = PS_CMD12b3;
			goto consume;

 		case PA_CMD12b3_TOK_SYMBOL_CMD12b3:
			state = PS_CMD12b3;
			goto consume;

 		case PA_CMD12b3_TOK_RP_R0:
			state = PS_R0;
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
			int_stack_push(pstack, PS_TRM2);
			fprintf(stderr, "pushing %d\n", PS_TRM2);
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
			int_stack_push(pstack, PS_TRM2);
			fprintf(stderr, "pushing %d\n", PS_TRM2);
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
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
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
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_SRT0;
			goto consume;

 		case PA_TRM5_TOK_LP_TRM5a:
			state = PS_TRM5a;
			goto consume;

 		case PA_TRM5a_TOK_LP_TRM5b:
			state = PS_TRM5b;
			goto consume;

 		case PA_TRM5b_TOK_SYMBOL_TRM0:
			int_stack_push(pstack, PS_TRM5c);
			fprintf(stderr, "pushing %d\n", PS_TRM5c);
			state = PS_TRM0;
			goto consume;

 		case PA_TRM5c_TOK_RP_TRM5d:
			state = PS_TRM5d;
			goto consume;

 		case PA_TRM5d_TOK_LP_TRM5b:
			state = PS_TRM5b;
			goto consume;

 		case PA_TRM5d_TOK_RP_TRM0:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			state = PS_TRM0;
			goto consume;

 		case PA_TRM6_TOK_LP_SVL0a:
			int_stack_push(pstack, PS_R0);
			fprintf(stderr, "pushing %d\n", PS_R0);
			int_stack_push(pstack, PS_TRM0);
			fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_SVL0a;
			goto skip;

 		case PA_TRM7_TOK_RW_UNDERSCORE_TRM3:
			int_stack_push(pstack, PS_TRM7a);
			fprintf(stderr, "pushing %d\n", PS_TRM7a);
			int_stack_push(pstack, PS_TRM0);
			fprintf(stderr, "pushing %d\n", PS_TRM0);
			state = PS_TRM3;
			goto consume;

 		case PA_TRM7_TOK_RW_AS_TRM4:
			int_stack_push(pstack, PS_TRM7a);
			fprintf(stderr, "pushing %d\n", PS_TRM7a);
			int_stack_push(pstack, PS_TRM0);
			fprintf(stderr, "pushing %d\n", PS_TRM0);
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
			int_stack_push(pstack, PS_SVL3);
			fprintf(stderr, "pushing %d\n", PS_SVL3);
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
			int_stack_push(pstack, PS_SRT2);
			fprintf(stderr, "pushing %d\n", PS_SRT2);
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
			int_stack_push(pstack, PS_SRT2);
			fprintf(stderr, "pushing %d\n", PS_SRT2);
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
			int_stack_push(pstack, PS_SRT2);
			fprintf(stderr, "pushing %d\n", PS_SRT2);
			state = PS_SRT0;
			goto consume;

 		case PA_ANY_WC_ERR:
			state = PS_ERR;
			goto skip;

	}

	return 1;
}

