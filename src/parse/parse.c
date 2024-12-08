
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "parse/parse.h"

/**
 * Initializes `parser` to use `filename` as input. Returns 0 on success, the 
 * result of `init_file_lexer` otherwise.
 */
int init_parser(parser_t *parser, const char *filename)
{
	int status = init_file_lexer(&parser->lex, filename);
	if (status) {
		return status;
	}

    init_int_stack(&parser->sstack);
    init_pstack(&parser->pstack, filename);
    init_context(&parser->ctx);
	parser->filename = filename;
	return 0;
}

void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
    delete_int_stack(&parser->sstack);
    delete_pstack(&parser->pstack);
}

typedef enum parse_state {
	CMD0,
	CMD1,
	CMD10,
	CMD11,
	CMD11a,
	CMD11b,
	CMD11c,
	CMD11d,
	CMD11e,
	CMD12,
	CMD12a,
	CMD12b,
	CMD12b0,
	CMD12c,
	CMD12c0,
	CMD12c1,
	CMD12c2,
	CMD12c3,
	CMD12d,
	CMD12d0,
	CMD2,
	CMD3,
	CMD4,
	CMD5,
	CMD5a,
	CMD5b,
	CMD6,
	CMD6a,
	CMD6b,
	CMD6c,
	CMD7,
	CMD7a,
	CMD8,
	CMD8a,
	CMD8b,
	CMD8c,
	CMD9,
	DONE,
	ERR,
	ERR_CMD,
	ERR_LP_EOF,
	ERR_RP,
	ERR_STR,
	ERR_SYM,
	R0,
	SRT0,
	SRT1,
	SRT2,
	SRT3,
	SRT3a,
	SRT3b,
	SRT4,
	SRT4a,
	SRT4b,
	SRTL0,
	SRTL1,
	STR0,
	SVL0,
	SVL0a,
	SVL0b,
	SVL1,
	SVL2,
	SVL3,
	TRM0,
	TRM1,
	TRM2,
	TRM3,
	TRM3a,
	TRM3b,
	TRM4,
	TRM4a,
	TRM4b,
	TRM4c,
	TRM4d,
	TRM5,
	TRM5a,
	TRM5b,
	TRM5c,
	TRM5d,
	TRM6,
	TRM7,
	TRM7a,
} parse_state_t;

typedef enum parse_action {
	CMD0_EOF_DONE,
	CMD0_LP_CMD1,
	CMD0_WC_ERR_LP_EOF,
	CMD10_SYMBOL_SRT0,
	CMD11_SYMBOL_CMD11a,
	CMD11a_KW_INIT_TRM0,
	CMD11a_KW_INPUT_SVL0,
	CMD11a_KW_INV_TRM0,
	CMD11a_KW_LOCAL_SVL0,
	CMD11a_KW_OUTPUT_SVL0,
	CMD11a_KW_SUBSYS_CMD11b,
	CMD11a_KW_TRANS_TRM0,
	CMD11a_RP_DONE,
	CMD11b_LP_CMD11c,
	CMD11c_SYMBOL_CMD11d,
	CMD11d_LP_CMD11e,
	CMD11e_RP_R0,
	CMD11e_SYMBOL_CMD11e,
	CMD12_SYMBOL_CMD12a,
	CMD12a_KW_ASSUME_CMD12b,
	CMD12a_KW_CURRENT_CMD12b,
	CMD12a_KW_FAIR_CMD12b,
	CMD12a_KW_INPUT_SVL0,
	CMD12a_KW_LOCAL_SVL0,
	CMD12a_KW_OUTPUT_SVL0,
	CMD12a_KW_QUERIES_CMD12d,
	CMD12a_KW_QUERY_CMD12c,
	CMD12a_KW_REACH_CMD12b,
	CMD12a_RP_DONE,
	CMD12b0_SYMBOL_TRM0,
	CMD12b_LP_CMD12b0,
	CMD12c0_SYMBOL_CMD12c1,
	CMD12c1_LP_CMD12c2,
	CMD12c2_SYMBOL_CMD12c3,
	CMD12c3_RP_R0,
	CMD12c3_SYMBOL_CMD12c3,
	CMD12c_LP_CMD12c0,
	CMD12d0_LP_CMD12c,
	CMD12d0_RP_DONE,
	CMD12d_LP_CMD12c,
	CMD1_RW_ASSERT_TRM0,
	CMD1_RW_CHECK_SYS_CMD12,
	CMD1_RW_DECLARE_CONST_CMD9,
	CMD1_RW_DECLARE_ENUM_SORT_CMD8,
	CMD1_RW_DECLARE_FUN_CMD5,
	CMD1_RW_DECLARE_SORT_CMD7,
	CMD1_RW_DEFINE_CONST_CMD10,
	CMD1_RW_DEFINE_FUN_CMD4,
	CMD1_RW_DEFINE_SORT_CMD6,
	CMD1_RW_DEFINE_SYS_CMD11,
	CMD1_RW_ECHO_CMD2,
	CMD1_RW_EXIT_R0,
	CMD1_RW_RESET_R0,
	CMD1_RW_SET_LOGIC_CMD3,
	CMD1_WC_ERR_CMD,
	CMD2_STRING_R0,
	CMD2_WC_ERR_STR,
	CMD3_SYMBOL_R0,
	CMD3_WC_ERR_SYM,
	CMD4_SYMBOL_SVL0,
	CMD4_WC_ERR_SYM,
	CMD5_SYMBOL_CMD5a,
	CMD5_WC_ERR_SYM,
	CMD5a_LP_CMD5b,
	CMD5b_RP_STR0,
	CMD5b_WC_SRT0,
	CMD6_SYMBOL_CMD6a,
	CMD6a_LP_CMD6b,
	CMD6b_RP_CMD6c,
	CMD6b_SYMBOL_CMD6b,
	CMD7_SYMBOL_CMD7a,
	CMD7a_NUMERAL_R0,
	CMD8_SYMBOL_CMD8a,
	CMD8a_LP_CMD8b,
	CMD8b_SYMBOL_CMD8c,
	CMD8c_RP_R0,
	CMD8c_SYMBOL_CMD8c,
	CMD9_SYMBOL_SRT0,
	ERR_CMD_WC_ERR,
	ERR_LP_EOF_WC_ERR,
	ERR_RP_WC_ERR,
	ERR_STR_WC_ERR,
	ERR_SYM_WC_ERR,
	ERR_WC_ERR,
	R0_RP_DONE,
	R0_WC_ERR_RP,
	SRT0_LP_SRT1,
	SRT0_SYMBOL_DONE,
	SRT1_LP_SRT4,
	SRT1_RW_UNDERSCORE_SRT3,
	SRT1_SYMBOL_SRT0,
	SRT2_RP_DONE,
	SRT2_WC_SRT0,
	SRT3_SYMBOL_SRT3a,
	SRT3a_NUMERAL_SRT3b,
	SRT3b_NUMERAL_SRT3b,
	SRT3b_RP_DONE,
	SRT4_SYMBOL_SRT4a,
	SRT4a_NUMERAL_SRT4b,
	SRT4b_NUMERAL_SRT4b,
	SRT4b_RP_SRT0,
	SRTL0_LP_SRTL1,
	SRTL1_RP_DONE,
	SRTL1_WC_SRT0,
	SVL0_LP_SVL1,
	SVL0a_LP_SVL0b,
	SVL0b_LP_SVL2,
	SVL1_LP_SVL2,
	SVL1_RP_DONE,
	SVL2_WC_SRT0,
	SVL3_RP_SVL1,
	TRM0_BINARY_DONE,
	TRM0_DECIMAL_DONE,
	TRM0_HEX_DONE,
	TRM0_LP_TRM1,
	TRM0_NUMERAL_DONE,
	TRM0_STRING_DONE,
	TRM0_SYMBOL_DONE,
	TRM1_LP_TRM7,
	TRM1_RW_AS_TRM4,
	TRM1_RW_EXISTS_TRM6,
	TRM1_RW_FORALL_TRM6,
	TRM1_RW_LET_TRM5,
	TRM1_RW_UNDERSCORE_TRM3,
	TRM1_SYMBOL_TRM0,
	TRM2_RP_DONE,
	TRM2_WC_TRM0,
	TRM3_SYMBOL_TRM3a,
	TRM3a_NUMERAL_TRM3b,
	TRM3b_NUMERAL_TRM3b,
	TRM3b_RP_TRM0,
	TRM4_LP_TRM4a,
	TRM4_SYMBOL_SRT0,
	TRM4a_RW_UNDERSCORE_TRM4b,
	TRM4b_SYMBOL_TRM4c,
	TRM4c_NUMERAL_TRM4d,
	TRM4d_NUMERAL_TRM4d,
	TRM4d_RP_SRT0,
	TRM5_LP_TRM5a,
	TRM5a_LP_TRM5b,
	TRM5b_SYMBOL_TRM0,
	TRM5c_RP_TRM5d,
	TRM5d_LP_TRM5b,
	TRM5d_RP_TRM0,
	TRM6_LP_SVL0a,
	TRM7_RW_AS_TRM4,
	TRM7_RW_UNDERSCORE_TRM3,
	TRM7a_RP_DONE,
	TRM7a_WC_TRM0,
} parse_action_t;

const int def[82] = {
	CMD0_WC_ERR_LP_EOF,
	CMD1_WC_ERR_CMD,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	CMD2_WC_ERR_STR,
	CMD3_WC_ERR_SYM,
	CMD4_WC_ERR_SYM,
	CMD5_WC_ERR_SYM,
	ERR_WC_ERR,
	CMD5b_WC_SRT0,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_CMD_WC_ERR,
	ERR_LP_EOF_WC_ERR,
	ERR_RP_WC_ERR,
	ERR_STR_WC_ERR,
	ERR_SYM_WC_ERR,
	R0_WC_ERR_RP,
	ERR_WC_ERR,
	ERR_WC_ERR,
	SRT2_WC_SRT0,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	SRTL1_WC_SRT0,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	SVL2_WC_SRT0,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	TRM2_WC_TRM0,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	ERR_WC_ERR,
	TRM7a_WC_TRM0,
};

const int base[82] = {
	0,
	0,
	0,
	1,
	0,
	2,
	2,
	3,
	3,
	4,
	38,
	5,
	5,
	6,
	6,
	7,
	7,
	8,
	8,
	10,
	6,
	9,
	10,
	11,
	13,
	13,
	12,
	15,
	15,
	0,
	13,
	15,
	14,
	40,
	16,
	40,
	17,
	0,
	0,
	0,
	0,
	0,
	0,
	0,
	41,
	43,
	64,
	43,
	19,
	43,
	65,
	22,
	67,
	72,
	76,
	82,
	0,
	84,
	85,
	87,
	90,
	0,
	87,
	92,
	100,
	92,
	53,
	99,
	101,
	104,
	94,
	60,
	105,
	107,
	112,
	113,
	72,
	118,
	120,
	122,
	112,
	123,
};

const int check[180] = {
	0,
	0,
	4,
	5,
	7,
	8,
	11,
	13,
	15,
	18,
	17,
	19,
	19,
	20,
	24,
	25,
	27,
	28,
	31,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	4,
	4,
	4,
	4,
	4,
	4,
	4,
	10,
	33,
	35,
	44,
	45,
	47,
	49,
	2,
	3,
	6,
	8,
	9,
	12,
	14,
	16,
	17,
	21,
	22,
	23,
	26,
	30,
	32,
	28,
	34,
	36,
	46,
	48,
	50,
	50,
	51,
	52,
	10,
	10,
	10,
	53,
	53,
	46,
	54,
	10,
	10,
	10,
	10,
	10,
	10,
	55,
	57,
	58,
	35,
	59,
	62,
	45,
	60,
	60,
	63,
	65,
	63,
	63,
	63,
	63,
	63,
	66,
	64,
	67,
	68,
	68,
	69,
	70,
	71,
	72,
	73,
	73,
	46,
	64,
	74,
	75,
	64,
	64,
	64,
	64,
	76,
	77,
	78,
	78,
	79,
	80,
	81,
	82,
	80,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	63,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	64,
	82,
	82,
	82,
	69,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
	82,
};

const int value[180] = {
	0,
	1,
	12,
	13,
	15,
	16,
	30,
	36,
	32,
	39,
	34,
	37,
	38,
	55,
	63,
	64,
	67,
	68,
	71,
	49,
	41,
	45,
	43,
	42,
	44,
	48,
	46,
	47,
	51,
	53,
	50,
	52,
	40,
	6,
	9,
	8,
	5,
	11,
	7,
	10,
	28,
	73,
	75,
	84,
	86,
	91,
	94,
	3,
	4,
	14,
	17,
	18,
	29,
	31,
	33,
	35,
	57,
	59,
	61,
	66,
	70,
	72,
	69,
	74,
	77,
	88,
	93,
	96,
	95,
	97,
	98,
	22,
	24,
	23,
	100,
	99,
	89,
	101,
	19,
	27,
	21,
	20,
	26,
	25,
	102,
	104,
	105,
	76,
	106,
	110,
	87,
	107,
	108,
	114,
	125,
	115,
	112,
	111,
	113,
	116,
	127,
	118,
	128,
	130,
	129,
	131,
	133,
	134,
	135,
	137,
	136,
	90,
	123,
	138,
	139,
	119,
	122,
	120,
	121,
	140,
	141,
	142,
	143,
	144,
	146,
	147,
	38,
	145,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	117,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	124,
	38,
	38,
	38,
	132,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
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
    char_buffer_t *str;
    const char *filename;
    token_type_t token;
    int_stack_t *sstack; // state stack
    parse_state_t state;
    parse_action_t action;
    loc_t loc;
    pstack_t *pstack; // parse stack
    context_t *ctx;
    int exception;

    lex = &parser->lex;
    str = &lex->buffer;
    filename = parser->filename;
    sstack = &parser->sstack;
    state = CMD0;
    pstack = &parser->pstack;
    ctx = &parser->ctx;

consume:
    if (state == DONE && sstack->size == 0) {
		pstack_eval_frame(pstack, ctx);
		return token == TOK_EOF ? 1 : 0;
	}

    lexer_next_token(lex);
	token = lex->tok_type;
    loc = lex->loc;

skip:
    exception = setjmp(pstack->env);
    if (exception != 0) {
        return exception;
    }
    
    if (state == ERR) {
        return -1;
    } 
    
    if (state == DONE) {
		pstack_eval_frame(pstack, ctx);
		if (sstack->size == 0) {
            return token == TOK_EOF ? 1 : 0;
		}
        state = int_stack_pop(sstack);
    }

    action = get_action(state, token);

#ifdef DEBUG_PARSER
    fprintf(stderr, "state: %d, token: '%s' (%d), action: %d\n", 
        state, token_type_str[token], token, action);
#endif

    switch(action) {
		case ERR_RP_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "expected ')'");
			state = ERR;
			goto skip;

 		case ERR_LP_EOF_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "expected ')' or EOF");
			state = ERR;
			goto skip;

 		case ERR_CMD_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "expected command symbol");
			state = ERR;
			goto skip;

 		case ERR_STR_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "expected string");
			state = ERR;
			goto skip;

 		case ERR_SYM_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "expected symbol");
			state = ERR;
			goto skip;

 		case R0_RP_DONE:
			state = DONE;
			goto consume;

 		case R0_WC_ERR_RP:
			state = ERR_RP;
			goto consume;

 		case CMD0_LP_CMD1:
			state = CMD1;
			goto consume;

 		case CMD0_EOF_DONE:
			state = DONE;
			goto skip;

 		case CMD0_WC_ERR_LP_EOF:
			state = ERR_LP_EOF;
			goto skip;

 		case CMD1_RW_EXIT_R0:
			pstack_push_frame(pstack, FRM_EXIT, loc);
			state = R0;
			goto consume;

 		case CMD1_RW_RESET_R0:
			pstack_push_frame(pstack, FRM_RESET, loc);
			state = R0;
			goto consume;

 		case CMD1_RW_ASSERT_TRM0:
			pstack_push_frame(pstack, FRM_ASSERT, loc);
			int_stack_push(sstack, R0);
			state = TRM0;
			goto consume;

 		case CMD1_RW_ECHO_CMD2:
			pstack_push_frame(pstack, FRM_ECHO, loc);
			state = CMD2;
			goto consume;

 		case CMD1_RW_SET_LOGIC_CMD3:
			pstack_push_frame(pstack, FRM_SET_LOGIC, loc);
			state = CMD3;
			goto consume;

 		case CMD1_RW_DEFINE_FUN_CMD4:
			pstack_push_frame(pstack, FRM_DEFINE_FUN, loc);
			state = CMD4;
			goto consume;

 		case CMD1_RW_DECLARE_FUN_CMD5:
			pstack_push_frame(pstack, FRM_DECLARE_FUN, loc);
			state = CMD5;
			goto consume;

 		case CMD1_RW_DEFINE_SORT_CMD6:
			pstack_push_frame(pstack, FRM_DEFINE_SORT, loc);
			state = CMD6;
			goto consume;

 		case CMD1_RW_DECLARE_SORT_CMD7:
			pstack_push_frame(pstack, FRM_DECLARE_SORT, loc);
			state = CMD7;
			goto consume;

 		case CMD1_RW_DECLARE_ENUM_SORT_CMD8:
			pstack_push_frame(pstack, FRM_DECLARE_ENUM_SORT, loc);
			state = CMD8;
			goto consume;

 		case CMD1_RW_DECLARE_CONST_CMD9:
			pstack_push_frame(pstack, FRM_DECLARE_CONST, loc);
			state = CMD9;
			goto consume;

 		case CMD1_RW_DEFINE_CONST_CMD10:
			pstack_push_frame(pstack, FRM_DEFINE_CONST, loc);
			state = CMD10;
			goto consume;

 		case CMD1_RW_DEFINE_SYS_CMD11:
			pstack_push_frame(pstack, FRM_DEFINE_SYS, loc);
			state = CMD11;
			goto consume;

 		case CMD1_RW_CHECK_SYS_CMD12:
			pstack_push_frame(pstack, FRM_CHECK_SYS, loc);
			state = CMD12;
			goto consume;

 		case CMD1_WC_ERR_CMD:
			state = ERR_CMD;
			goto skip;

 		case CMD2_STRING_R0:
			state = R0;
			goto consume;

 		case CMD2_WC_ERR_STR:
			state = ERR_STR;
			goto skip;

 		case CMD3_SYMBOL_R0:
			pstack_push_symbol(pstack, str, loc);
			state = R0;
			goto consume;

 		case CMD3_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD4_SYMBOL_SVL0:
			pstack_set_vars_logic(pstack);
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM0);
			int_stack_push(sstack, SRT0);
			state = SVL0;
			goto consume;

 		case CMD4_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD5_SYMBOL_CMD5a:
			pstack_push_symbol(pstack, str, loc);
			state = CMD5a;
			goto consume;

 		case CMD5a_LP_CMD5b:
			state = CMD5b;
			goto consume;

 		case CMD5b_RP_STR0:
			int_stack_push(sstack, R0);
			state = STR0;
			goto consume;

 		case CMD5b_WC_SRT0:
			int_stack_push(sstack, CMD5b);
			state = SRT0;
			goto skip;

 		case CMD5_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD6_SYMBOL_CMD6a:
			pstack_push_symbol(pstack, str, loc);
			state = CMD6a;
			goto consume;

 		case CMD6a_LP_CMD6b:
			state = CMD6b;
			goto consume;

 		case CMD6b_SYMBOL_CMD6b:
			pstack_push_symbol(pstack, str, loc);
			state = CMD6b;
			goto consume;

 		case CMD6b_RP_CMD6c:
			int_stack_push(sstack, R0);
			state = CMD6c;
			goto consume;

 		case CMD7_SYMBOL_CMD7a:
			pstack_push_symbol(pstack, str, loc);
			state = CMD7a;
			goto consume;

 		case CMD7a_NUMERAL_R0:
			state = R0;
			goto consume;

 		case CMD8_SYMBOL_CMD8a:
			pstack_push_symbol(pstack, str, loc);
			state = CMD8a;
			goto consume;

 		case CMD8a_LP_CMD8b:
			state = CMD8b;
			goto consume;

 		case CMD8b_SYMBOL_CMD8c:
			state = CMD8c;
			goto consume;

 		case CMD8c_SYMBOL_CMD8c:
			state = CMD8c;
			goto consume;

 		case CMD8c_RP_R0:
			state = R0;
			goto consume;

 		case CMD9_SYMBOL_SRT0:
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case CMD10_SYMBOL_SRT0:
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM0);
			state = SRT0;
			goto consume;

 		case CMD11_SYMBOL_CMD11a:
			state = CMD11a;
			goto consume;

 		case CMD11a_KW_INPUT_SVL0:
			pstack_set_vars_input(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_OUTPUT_SVL0:
			pstack_set_vars_output(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_LOCAL_SVL0:
			pstack_set_vars_local(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_INIT_TRM0:
			int_stack_push(sstack, CMD11a);
			state = TRM0;
			goto consume;

 		case CMD11a_KW_TRANS_TRM0:
			int_stack_push(sstack, CMD11a);
			state = TRM0;
			goto consume;

 		case CMD11a_KW_INV_TRM0:
			int_stack_push(sstack, CMD11a);
			state = TRM0;
			goto consume;

 		case CMD11a_KW_SUBSYS_CMD11b:
			int_stack_push(sstack, CMD11a);
			state = CMD11b;
			goto consume;

 		case CMD11a_RP_DONE:
			state = DONE;
			goto consume;

 		case CMD11b_LP_CMD11c:
			state = CMD11c;
			goto consume;

 		case CMD11c_SYMBOL_CMD11d:
			state = CMD11d;
			goto consume;

 		case CMD11d_LP_CMD11e:
			state = CMD11e;
			goto consume;

 		case CMD11e_SYMBOL_CMD11e:
			state = CMD11e;
			goto consume;

 		case CMD11e_RP_R0:
			state = R0;
			goto consume;

 		case CMD12_SYMBOL_CMD12a:
			state = CMD12a;
			goto consume;

 		case CMD12a_KW_INPUT_SVL0:
			pstack_set_vars_input(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_OUTPUT_SVL0:
			pstack_set_vars_output(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_LOCAL_SVL0:
			pstack_set_vars_local(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_ASSUME_CMD12b:
			int_stack_push(sstack, CMD12a);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_CURRENT_CMD12b:
			int_stack_push(sstack, CMD12a);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_REACH_CMD12b:
			int_stack_push(sstack, CMD12a);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_FAIR_CMD12b:
			int_stack_push(sstack, CMD12a);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_QUERY_CMD12c:
			int_stack_push(sstack, CMD12a);
			state = CMD12c;
			goto consume;

 		case CMD12a_KW_QUERIES_CMD12d:
			int_stack_push(sstack, CMD12a);
			state = CMD12d;
			goto consume;

 		case CMD12a_RP_DONE:
			state = DONE;
			goto consume;

 		case CMD12b_LP_CMD12b0:
			state = CMD12b0;
			goto consume;

 		case CMD12b0_SYMBOL_TRM0:
			int_stack_push(sstack, R0);
			state = TRM0;
			goto consume;

 		case CMD12c_LP_CMD12c0:
			state = CMD12c0;
			goto consume;

 		case CMD12c0_SYMBOL_CMD12c1:
			state = CMD12c1;
			goto consume;

 		case CMD12c1_LP_CMD12c2:
			state = CMD12c2;
			goto consume;

 		case CMD12c2_SYMBOL_CMD12c3:
			state = CMD12c3;
			goto consume;

 		case CMD12c3_SYMBOL_CMD12c3:
			state = CMD12c3;
			goto consume;

 		case CMD12c3_RP_R0:
			state = R0;
			goto consume;

 		case CMD12d_LP_CMD12c:
			int_stack_push(sstack, CMD12d0);
			state = CMD12c;
			goto consume;

 		case CMD12d0_LP_CMD12c:
			int_stack_push(sstack, CMD12d0);
			state = CMD12c;
			goto skip;

 		case CMD12d0_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM0_NUMERAL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_numeral(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM0_DECIMAL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_decimal(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM0_HEX_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM0_BINARY_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM0_STRING_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM0_SYMBOL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_symbol(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM0_LP_TRM1:
			pstack_push_frame(pstack, FRM_TERM, loc);
			state = TRM1;
			goto consume;

 		case TRM1_SYMBOL_TRM0:
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, TRM2);
			state = TRM0;
			goto consume;

 		case TRM1_RW_UNDERSCORE_TRM3:
			state = TRM3;
			goto consume;

 		case TRM1_RW_AS_TRM4:
			state = TRM4;
			goto consume;

 		case TRM1_RW_LET_TRM5:
			state = TRM5;
			goto consume;

 		case TRM1_RW_FORALL_TRM6:
			state = TRM6;
			goto consume;

 		case TRM1_RW_EXISTS_TRM6:
			state = TRM6;
			goto consume;

 		case TRM1_LP_TRM7:
			state = TRM7;
			goto consume;

 		case TRM2_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM2_WC_TRM0:
			int_stack_push(sstack, TRM2);
			state = TRM0;
			goto skip;

 		case TRM3_SYMBOL_TRM3a:
			pstack_push_symbol(pstack, str, loc);
			state = TRM3a;
			goto consume;

 		case TRM3a_NUMERAL_TRM3b:
			pstack_push_numeral(pstack, str, loc);
			state = TRM3b;
			goto consume;

 		case TRM3b_NUMERAL_TRM3b:
			pstack_push_numeral(pstack, str, loc);
			state = TRM3b;
			goto consume;

 		case TRM3b_RP_TRM0:
			int_stack_push(sstack, TRM2);
			state = TRM0;
			goto consume;

 		case TRM4_SYMBOL_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case TRM4_LP_TRM4a:
			state = TRM4a;
			goto consume;

 		case TRM4a_RW_UNDERSCORE_TRM4b:
			state = TRM4b;
			goto consume;

 		case TRM4b_SYMBOL_TRM4c:
			state = TRM4c;
			goto consume;

 		case TRM4c_NUMERAL_TRM4d:
			state = TRM4d;
			goto consume;

 		case TRM4d_NUMERAL_TRM4d:
			state = TRM4d;
			goto consume;

 		case TRM4d_RP_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case TRM5_LP_TRM5a:
			state = TRM5a;
			goto consume;

 		case TRM5a_LP_TRM5b:
			state = TRM5b;
			goto consume;

 		case TRM5b_SYMBOL_TRM0:
			int_stack_push(sstack, TRM5c);
			state = TRM0;
			goto consume;

 		case TRM5c_RP_TRM5d:
			state = TRM5d;
			goto consume;

 		case TRM5d_LP_TRM5b:
			state = TRM5b;
			goto consume;

 		case TRM5d_RP_TRM0:
			int_stack_push(sstack, R0);
			state = TRM0;
			goto consume;

 		case TRM6_LP_SVL0a:
			pstack_set_vars_logic(pstack);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM0);
			state = SVL0a;
			goto skip;

 		case TRM7_RW_UNDERSCORE_TRM3:
			state = TRM3;
			goto consume;

 		case TRM7_RW_AS_TRM4:
			int_stack_push(sstack, TRM7a);
			int_stack_push(sstack, TRM0);
			state = TRM4;
			goto consume;

 		case TRM7a_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM7a_WC_TRM0:
			state = TRM0;
			goto skip;

 		case SVL0_LP_SVL1:
			pstack_push_frame(pstack, FRM_NOOP, loc);
			state = SVL1;
			goto consume;

 		case SVL0a_LP_SVL0b:
			pstack_push_frame(pstack, FRM_NOOP, loc);
			state = SVL0b;
			goto consume;

 		case SVL0b_LP_SVL2:
			state = SVL2;
			goto consume;

 		case SVL1_LP_SVL2:
			pstack_push_frame(pstack, FRM_VAR_DECL, loc);
			state = SVL2;
			goto consume;

 		case SVL1_RP_DONE:
			state = DONE;
			goto consume;

 		case SVL2_WC_SRT0:
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, SVL3);
			state = SRT0;
			goto consume;

 		case SVL3_RP_SVL1:
			pstack_eval_frame(pstack, ctx);
			state = SVL1;
			goto consume;

 		case SRTL0_LP_SRTL1:
			pstack_push_frame(pstack, FRM_NOOP, loc);
			state = SRTL1;
			goto consume;

 		case SRTL1_RP_DONE:
			state = DONE;
			goto consume;

 		case SRTL1_WC_SRT0:
			int_stack_push(sstack, SRTL1);
			state = SRT0;
			goto skip;

 		case SRT0_SYMBOL_DONE:
			pstack_push_frame(pstack, FRM_SORT, loc);
			pstack_push_symbol(pstack, str, loc);
			state = DONE;
			goto consume;

 		case SRT0_LP_SRT1:
			pstack_push_frame(pstack, FRM_SORT, loc);
			state = SRT1;
			goto consume;

 		case SRT1_SYMBOL_SRT0:
			pstack_push_frame(pstack, FRM_SORT, loc);
			pstack_push_symbol(pstack, str, loc);
			int_stack_push(sstack, SRT2);
			state = SRT0;
			goto consume;

 		case SRT1_RW_UNDERSCORE_SRT3:
			state = SRT3;
			goto consume;

 		case SRT1_LP_SRT4:
			pstack_push_frame(pstack, FRM_SORT, loc);
			state = SRT4;
			goto consume;

 		case SRT2_RP_DONE:
			state = DONE;
			goto consume;

 		case SRT2_WC_SRT0:
			int_stack_push(sstack, SRT2);
			state = SRT0;
			goto skip;

 		case SRT3_SYMBOL_SRT3a:
			pstack_push_symbol(pstack, str, loc);
			state = SRT3a;
			goto consume;

 		case SRT3a_NUMERAL_SRT3b:
			pstack_push_numeral(pstack, str, loc);
			state = SRT3b;
			goto consume;

 		case SRT3b_NUMERAL_SRT3b:
			pstack_push_numeral(pstack, str, loc);
			state = SRT3b;
			goto consume;

 		case SRT3b_RP_DONE:
			state = DONE;
			goto consume;

 		case SRT4_SYMBOL_SRT4a:
			pstack_push_symbol(pstack, str, loc);
			state = SRT4a;
			goto consume;

 		case SRT4a_NUMERAL_SRT4b:
			pstack_push_numeral(pstack, str, loc);
			state = SRT4b;
			goto consume;

 		case SRT4b_NUMERAL_SRT4b:
			pstack_push_numeral(pstack, str, loc);
			state = SRT4b;
			goto consume;

 		case SRT4b_RP_SRT0:
			int_stack_push(sstack, SRT2);
			state = SRT0;
			goto consume;

 		case ERR_WC_ERR:
			PRINT_ERROR_LOC(filename, loc, "syntax error");
			state = ERR;
			goto skip;

	}

	return 1;
}

