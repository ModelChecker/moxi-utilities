
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
	CMD11f,
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
	SVL0,
	SVL0a,
	SVL0b,
	SVL1,
	SVL2,
	SVL3,
	TRM0,
	TRM0next,
	TRM1,
	TRM2,
	TRM3,
	TRM4,
	TRM4a,
	TRM4b,
	TRM5,
	TRM5a,
	TRM5b,
	TRM5c,
	TRM5d,
	TRM6,
	TRM6a,
	TRM6b,
	TRM6c,
	TRM6d,
	TRM7,
	TRM8,
	TRM8a,
} parse_state_t;

typedef enum parse_action {
	CMD0_EOF_DONE,
	CMD0_LP_CMD1,
	CMD0_WC_ERR_LP_EOF,
	CMD10_SYMBOL_SRT0,
	CMD11_SYMBOL_DONE,
	CMD11a_KW_INIT_TRM0,
	CMD11a_KW_INPUT_SVL0,
	CMD11a_KW_INV_TRM0,
	CMD11a_KW_LOCAL_SVL0,
	CMD11a_KW_OUTPUT_SVL0,
	CMD11a_KW_SUBSYS_CMD11b,
	CMD11a_KW_TRANS_TRM0next,
	CMD11a_RP_DONE,
	CMD11b_LP_CMD11c,
	CMD11c_SYMBOL_CMD11d,
	CMD11d_LP_CMD11e,
	CMD11e_SYMBOL_CMD11f,
	CMD11f_RP_R0,
	CMD11f_SYMBOL_CMD11f,
	CMD12_SYMBOL_DONE,
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
	CMD4_SYMBOL_DONE,
	CMD4_WC_ERR_SYM,
	CMD5_SYMBOL_CMD5a,
	CMD5_WC_ERR_SYM,
	CMD5a_LP_CMD5b,
	CMD5b_RP_SRT0,
	CMD5b_WC_SRT0,
	CMD6_SYMBOL_CMD6a,
	CMD6a_LP_CMD6b,
	CMD6b_RP_SRT0,
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
	TRM0_WC_TRM1,
	TRM0next_WC_TRM1,
	TRM1_BINARY_DONE,
	TRM1_DECIMAL_DONE,
	TRM1_HEX_DONE,
	TRM1_LP_TRM2,
	TRM1_NUMERAL_DONE,
	TRM1_STRING_DONE,
	TRM1_SYMBOL_DONE,
	TRM2_LP_TRM8,
	TRM2_RW_AS_TRM5,
	TRM2_RW_EXISTS_TRM7,
	TRM2_RW_FORALL_TRM7,
	TRM2_RW_LET_TRM6,
	TRM2_RW_UNDERSCORE_TRM4,
	TRM2_SYMBOL_TRM1,
	TRM3_RP_DONE,
	TRM3_WC_TRM1,
	TRM4_SYMBOL_TRM4a,
	TRM4a_NUMERAL_TRM4b,
	TRM4b_NUMERAL_TRM4b,
	TRM4b_RP_TRM1,
	TRM5_LP_TRM5a,
	TRM5_SYMBOL_SRT0,
	TRM5a_RW_UNDERSCORE_TRM5b,
	TRM5b_SYMBOL_TRM5c,
	TRM5c_NUMERAL_TRM5d,
	TRM5d_NUMERAL_TRM5d,
	TRM5d_RP_SRT0,
	TRM6_LP_TRM6a,
	TRM6a_LP_TRM6b,
	TRM6b_SYMBOL_TRM1,
	TRM6c_RP_TRM6d,
	TRM6d_LP_TRM6b,
	TRM6d_RP_TRM1,
	TRM7_LP_SVL0a,
	TRM8_RW_AS_TRM5,
	TRM8_RW_UNDERSCORE_TRM4,
	TRM8a_RP_DONE,
	TRM8a_WC_TRM1,
} parse_action_t;

const int def[83] = {
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
	SVL2_WC_SRT0,
	ERR_WC_ERR,
	TRM0_WC_TRM1,
	TRM0next_WC_TRM1,
	ERR_WC_ERR,
	ERR_WC_ERR,
	TRM3_WC_TRM1,
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
	TRM8a_WC_TRM1,
};

const int base[83] = {
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
	5,
	38,
	4,
	6,
	6,
	7,
	7,
	8,
	9,
	8,
	11,
	3,
	10,
	11,
	12,
	13,
	13,
	13,
	15,
	15,
	14,
	15,
	16,
	40,
	17,
	40,
	18,
	0,
	0,
	0,
	0,
	0,
	0,
	0,
	41,
	43,
	65,
	43,
	20,
	43,
	66,
	23,
	71,
	73,
	83,
	83,
	85,
	87,
	88,
	90,
	0,
	91,
	0,
	0,
	93,
	101,
	93,
	54,
	100,
	102,
	105,
	95,
	61,
	106,
	108,
	113,
	114,
	73,
	119,
	121,
	123,
	113,
	124,
};

const int check[181] = {
	0,
	0,
	4,
	5,
	7,
	12,
	9,
	14,
	16,
	19,
	21,
	18,
	20,
	20,
	25,
	26,
	28,
	29,
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
	11,
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
	10,
	13,
	15,
	17,
	18,
	22,
	23,
	24,
	27,
	30,
	29,
	32,
	34,
	36,
	46,
	48,
	50,
	50,
	51,
	11,
	11,
	11,
	52,
	53,
	53,
	46,
	11,
	11,
	11,
	11,
	11,
	11,
	54,
	55,
	56,
	35,
	57,
	58,
	45,
	59,
	59,
	61,
	64,
	66,
	64,
	64,
	64,
	64,
	64,
	67,
	65,
	68,
	69,
	69,
	70,
	71,
	72,
	73,
	74,
	74,
	46,
	65,
	75,
	76,
	65,
	65,
	65,
	65,
	77,
	78,
	79,
	79,
	80,
	81,
	82,
	83,
	81,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	64,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	65,
	83,
	83,
	83,
	70,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
	83,
};

const int value[181] = {
	0,
	1,
	12,
	13,
	15,
	31,
	17,
	37,
	33,
	40,
	56,
	35,
	38,
	39,
	64,
	65,
	68,
	69,
	72,
	50,
	42,
	46,
	44,
	43,
	45,
	49,
	47,
	48,
	52,
	54,
	51,
	53,
	41,
	6,
	9,
	8,
	5,
	11,
	7,
	10,
	29,
	74,
	76,
	85,
	87,
	92,
	95,
	3,
	4,
	14,
	16,
	18,
	19,
	30,
	32,
	34,
	36,
	58,
	60,
	62,
	67,
	71,
	70,
	73,
	75,
	78,
	89,
	94,
	97,
	96,
	98,
	23,
	25,
	24,
	99,
	101,
	100,
	90,
	20,
	28,
	22,
	21,
	27,
	26,
	102,
	103,
	105,
	77,
	106,
	107,
	88,
	108,
	109,
	111,
	117,
	128,
	118,
	115,
	114,
	116,
	119,
	130,
	121,
	131,
	133,
	132,
	134,
	136,
	137,
	138,
	140,
	139,
	91,
	126,
	141,
	142,
	122,
	125,
	123,
	124,
	143,
	144,
	145,
	146,
	147,
	149,
	150,
	38,
	148,
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
	120,
	38,
	38,
	38,
	38,
	38,
	38,
	38,
	127,
	38,
	38,
	38,
	135,
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
    moxi_context_t *ctx;
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
			pstack_push_string(pstack, str, loc);
			state = R0;
			goto consume;

 		case CMD3_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD4_SYMBOL_DONE:
			pstack_set_vars_logic(pstack);
			pstack_push_string(pstack, str, loc);
			pstack_push_frame(pstack, FRM_PUSH_SCOPE, loc);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM0);
			int_stack_push(sstack, SRT0);
			int_stack_push(sstack, SVL0);
			state = DONE;
			goto consume;

 		case CMD4_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD5_SYMBOL_CMD5a:
			pstack_push_string(pstack, str, loc);
			state = CMD5a;
			goto consume;

 		case CMD5a_LP_CMD5b:
			state = CMD5b;
			goto consume;

 		case CMD5b_RP_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case CMD5b_WC_SRT0:
			int_stack_push(sstack, CMD5b);
			state = SRT0;
			goto skip;

 		case CMD5_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD6_SYMBOL_CMD6a:
			pstack_push_string(pstack, str, loc);
			state = CMD6a;
			goto consume;

 		case CMD6a_LP_CMD6b:
			state = CMD6b;
			goto consume;

 		case CMD6b_SYMBOL_CMD6b:
			pstack_push_string(pstack, str, loc);
			state = CMD6b;
			goto consume;

 		case CMD6b_RP_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case CMD7_SYMBOL_CMD7a:
			pstack_push_string(pstack, str, loc);
			state = CMD7a;
			goto consume;

 		case CMD7a_NUMERAL_R0:
			pstack_push_numeral(pstack, str, loc);
			state = R0;
			goto consume;

 		case CMD8_SYMBOL_CMD8a:
			pstack_push_string(pstack, str, loc);
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
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case CMD10_SYMBOL_SRT0:
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM0);
			state = SRT0;
			goto consume;

 		case CMD11_SYMBOL_DONE:
			pstack_push_string(pstack, str, loc);
			pstack_push_frame(pstack, FRM_PUSH_SCOPE, loc);
			int_stack_push(sstack, CMD11a);
			state = DONE;
			goto consume;

 		case CMD11a_KW_INPUT_SVL0:
			pstack_push_attr(pstack, TOK_KW_INPUT, loc);
			pstack_set_vars_input(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_OUTPUT_SVL0:
			pstack_push_attr(pstack, TOK_KW_OUTPUT, loc);
			pstack_set_vars_output(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_LOCAL_SVL0:
			pstack_push_attr(pstack, TOK_KW_LOCAL, loc);
			pstack_set_vars_local(pstack);
			int_stack_push(sstack, CMD11a);
			state = SVL0;
			goto consume;

 		case CMD11a_KW_INIT_TRM0:
			pstack_push_attr(pstack, TOK_KW_INIT, loc);
			int_stack_push(sstack, CMD11a);
			state = TRM0;
			goto consume;

 		case CMD11a_KW_TRANS_TRM0next:
			pstack_push_attr(pstack, TOK_KW_TRANS, loc);
			int_stack_push(sstack, CMD11a);
			state = TRM0next;
			goto consume;

 		case CMD11a_KW_INV_TRM0:
			pstack_push_attr(pstack, TOK_KW_INV, loc);
			int_stack_push(sstack, CMD11a);
			state = TRM0;
			goto consume;

 		case CMD11a_KW_SUBSYS_CMD11b:
			pstack_push_attr(pstack, TOK_KW_SUBSYS, loc);
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
			pstack_push_string(pstack, str, loc);
			state = CMD11d;
			goto consume;

 		case CMD11d_LP_CMD11e:
			state = CMD11e;
			goto consume;

 		case CMD11e_SYMBOL_CMD11f:
			pstack_push_string(pstack, str, loc);
			state = CMD11f;
			goto consume;

 		case CMD11f_SYMBOL_CMD11f:
			pstack_push_string(pstack, str, loc);
			state = CMD11f;
			goto consume;

 		case CMD11f_RP_R0:
			state = R0;
			goto consume;

 		case CMD12_SYMBOL_DONE:
			pstack_push_frame(pstack, FRM_PUSH_SCOPE, loc);
			int_stack_push(sstack, CMD12a);
			state = DONE;
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

 		case TRM0next_WC_TRM1:
			pstack_enable_next_vars(pstack);
			state = TRM1;
			goto skip;

 		case TRM0_WC_TRM1:
			pstack_disable_next_vars(pstack);
			state = TRM1;
			goto skip;

 		case TRM1_NUMERAL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_numeral(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM1_DECIMAL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_decimal(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM1_HEX_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM1_BINARY_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM1_STRING_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_error(pstack, loc);
			state = DONE;
			goto consume;

 		case TRM1_SYMBOL_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_string(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM1_LP_TRM2:
			pstack_push_frame(pstack, FRM_TERM, loc);
			state = TRM2;
			goto consume;

 		case TRM2_SYMBOL_TRM1:
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, TRM3);
			state = TRM1;
			goto consume;

 		case TRM2_RW_UNDERSCORE_TRM4:
			state = TRM4;
			goto consume;

 		case TRM2_RW_AS_TRM5:
			state = TRM5;
			goto consume;

 		case TRM2_RW_LET_TRM6:
			state = TRM6;
			goto consume;

 		case TRM2_RW_FORALL_TRM7:
			state = TRM7;
			goto consume;

 		case TRM2_RW_EXISTS_TRM7:
			state = TRM7;
			goto consume;

 		case TRM2_LP_TRM8:
			state = TRM8;
			goto consume;

 		case TRM3_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM3_WC_TRM1:
			int_stack_push(sstack, TRM3);
			state = TRM1;
			goto skip;

 		case TRM4_SYMBOL_TRM4a:
			pstack_push_string(pstack, str, loc);
			state = TRM4a;
			goto consume;

 		case TRM4a_NUMERAL_TRM4b:
			pstack_push_numeral(pstack, str, loc);
			state = TRM4b;
			goto consume;

 		case TRM4b_NUMERAL_TRM4b:
			pstack_push_numeral(pstack, str, loc);
			state = TRM4b;
			goto consume;

 		case TRM4b_RP_TRM1:
			int_stack_push(sstack, TRM3);
			state = TRM1;
			goto consume;

 		case TRM5_SYMBOL_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case TRM5_LP_TRM5a:
			state = TRM5a;
			goto consume;

 		case TRM5a_RW_UNDERSCORE_TRM5b:
			state = TRM5b;
			goto consume;

 		case TRM5b_SYMBOL_TRM5c:
			state = TRM5c;
			goto consume;

 		case TRM5c_NUMERAL_TRM5d:
			state = TRM5d;
			goto consume;

 		case TRM5d_NUMERAL_TRM5d:
			state = TRM5d;
			goto consume;

 		case TRM5d_RP_SRT0:
			int_stack_push(sstack, R0);
			state = SRT0;
			goto consume;

 		case TRM6_LP_TRM6a:
			state = TRM6a;
			goto consume;

 		case TRM6a_LP_TRM6b:
			state = TRM6b;
			goto consume;

 		case TRM6b_SYMBOL_TRM1:
			int_stack_push(sstack, TRM6c);
			state = TRM1;
			goto consume;

 		case TRM6c_RP_TRM6d:
			state = TRM6d;
			goto consume;

 		case TRM6d_LP_TRM6b:
			state = TRM6b;
			goto consume;

 		case TRM6d_RP_TRM1:
			int_stack_push(sstack, R0);
			state = TRM1;
			goto consume;

 		case TRM7_LP_SVL0a:
			pstack_set_vars_logic(pstack);
			int_stack_push(sstack, R0);
			int_stack_push(sstack, TRM1);
			state = SVL0a;
			goto skip;

 		case TRM8_RW_UNDERSCORE_TRM4:
			state = TRM4;
			goto consume;

 		case TRM8_RW_AS_TRM5:
			int_stack_push(sstack, TRM8a);
			int_stack_push(sstack, TRM1);
			state = TRM5;
			goto consume;

 		case TRM8a_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM8a_WC_TRM1:
			state = TRM1;
			goto skip;

 		case SVL0_LP_SVL1:
			pstack_push_frame(pstack, FRM_NOOP_KEEP, loc);
			state = SVL1;
			goto consume;

 		case SVL0a_LP_SVL0b:
			pstack_push_frame(pstack, FRM_NOOP_KEEP, loc);
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
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, SVL3);
			state = SRT0;
			goto consume;

 		case SVL3_RP_SVL1:
			pstack_eval_frame(pstack, ctx);
			state = SVL1;
			goto consume;

 		case SRTL0_LP_SRTL1:
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
			pstack_push_string(pstack, str, loc);
			state = DONE;
			goto consume;

 		case SRT0_LP_SRT1:
			pstack_push_frame(pstack, FRM_SORT, loc);
			state = SRT1;
			goto consume;

 		case SRT1_SYMBOL_SRT0:
			pstack_push_frame(pstack, FRM_SORT, loc);
			pstack_push_string(pstack, str, loc);
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
			pstack_push_string(pstack, str, loc);
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
			pstack_push_string(pstack, str, loc);
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

