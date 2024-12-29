
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
	CMD12b1,
	CMD12c,
	CMD12c0,
	CMD12c1,
	CMD12d,
	CMD12d0,
	CMD12d1,
	CMD12e,
	CMD12e0,
	CMD12e1,
	CMD12e2,
	CMD12e3,
	CMD12e4,
	CMD12f,
	CMD12f0,
	CMD12f1,
	CMD12f2,
	CMD12f3,
	CMD12f4,
	CMD12f5,
	CMD12f6,
	CMD2,
	CMD3,
	CMD4,
	CMD4a,
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
	TRM0nextinput,
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
	TRM6e,
	TRM7,
	TRM7a,
	TRM8,
	TRM8a,
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
	CMD11a_KW_TRANS_TRM0next,
	CMD11a_RP_DONE,
	CMD11b_LP_CMD11c,
	CMD11c_SYMBOL_CMD11d,
	CMD11d_LP_CMD11e,
	CMD11e_RP_CMD11f,
	CMD11e_SYMBOL_CMD11e,
	CMD11f_RP_CMD11a,
	CMD12_SYMBOL_CMD12a,
	CMD12a_KW_ASSUMPTION_CMD12b,
	CMD12a_KW_CURRENT_CMD12d,
	CMD12a_KW_FAIRNESS_CMD12b,
	CMD12a_KW_INPUT_SVL0,
	CMD12a_KW_LOCAL_SVL0,
	CMD12a_KW_OUTPUT_SVL0,
	CMD12a_KW_QUERIES_CMD12f,
	CMD12a_KW_QUERY_CMD12e,
	CMD12a_KW_REACHABLE_CMD12c,
	CMD12a_RP_DONE,
	CMD12b0_SYMBOL_TRM0nextinput,
	CMD12b1_RP_CMD12a,
	CMD12b_LP_CMD12b0,
	CMD12c0_SYMBOL_TRM0next,
	CMD12c1_RP_CMD12a,
	CMD12c_LP_CMD12c0,
	CMD12d0_SYMBOL_TRM0,
	CMD12d1_RP_CMD12a,
	CMD12d_LP_CMD12d0,
	CMD12e0_SYMBOL_CMD12e1,
	CMD12e1_LP_CMD12e2,
	CMD12e2_SYMBOL_CMD12e3,
	CMD12e3_RP_CMD12e4,
	CMD12e3_SYMBOL_CMD12e3,
	CMD12e4_RP_CMD12a,
	CMD12e_LP_CMD12e0,
	CMD12f0_LP_CMD12f1,
	CMD12f1_SYMBOL_CMD12f2,
	CMD12f2_LP_CMD12f3,
	CMD12f3_SYMBOL_CMD12f4,
	CMD12f4_RP_CMD12f5,
	CMD12f4_SYMBOL_CMD12f4,
	CMD12f5_RP_CMD12f6,
	CMD12f6_LP_CMD12f0,
	CMD12f6_RP_CMD12a,
	CMD12f_LP_CMD12f0,
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
	CMD4a_RP_DONE,
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
	SVL3_RP_DONE,
	TRM0_WC_TRM1,
	TRM0next_WC_TRM1,
	TRM0nextinput_WC_TRM1,
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
	TRM6c_RP_DONE,
	TRM6d_LP_TRM6b,
	TRM6d_RP_TRM1,
	TRM6e_RP_DONE,
	TRM7_LP_SVL0a,
	TRM7a_RP_DONE,
	TRM8_RW_AS_TRM5,
	TRM8_RW_UNDERSCORE_TRM4,
	TRM8a_RP_DONE,
	TRM8a_WC_TRM1,
} parse_action_t;

const unsigned int def[101] = {
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
	ERR_WC_ERR,
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
	TRM0nextinput_WC_TRM1,
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
	ERR_WC_ERR,
	ERR_WC_ERR,
	TRM8a_WC_TRM1,
};

const unsigned int base[101] = {
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
	4,
	38,
	6,
	5,
	6,
	8,
	6,
	8,
	10,
	7,
	10,
	12,
	8,
	13,
	9,
	13,
	14,
	16,
	17,
	10,
	40,
	11,
	40,
	41,
	43,
	39,
	12,
	14,
	60,
	16,
	63,
	63,
	19,
	66,
	66,
	22,
	67,
	27,
	74,
	29,
	75,
	37,
	0,
	0,
	0,
	0,
	0,
	0,
	0,
	83,
	85,
	87,
	87,
	43,
	88,
	90,
	47,
	92,
	94,
	97,
	98,
	100,
	101,
	102,
	103,
	0,
	104,
	0,
	0,
	0,
	111,
	108,
	105,
	61,
	107,
	125,
	110,
	107,
	74,
	126,
	128,
	132,
	134,
	89,
	135,
	137,
	138,
	140,
	140,
	131,
	142,
};

const unsigned int check[199] = {
	0,
	0,
	4,
	5,
	7,
	8,
	9,
	12,
	14,
	15,
	17,
	18,
	20,
	21,
	23,
	25,
	26,
	27,
	28,
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
	30,
	32,
	33,
	34,
	34,
	35,
	2,
	3,
	6,
	8,
	10,
	13,
	16,
	19,
	22,
	24,
	29,
	31,
	36,
	25,
	37,
	38,
	39,
	40,
	41,
	42,
	43,
	44,
	45,
	46,
	11,
	11,
	11,
	47,
	48,
	49,
	50,
	11,
	11,
	11,
	11,
	11,
	11,
	51,
	59,
	60,
	32,
	61,
	62,
	63,
	64,
	65,
	65,
	66,
	67,
	68,
	68,
	69,
	61,
	70,
	71,
	72,
	73,
	74,
	74,
	76,
	82,
	83,
	81,
	84,
	86,
	80,
	44,
	80,
	80,
	80,
	80,
	80,
	87,
	81,
	88,
	50,
	81,
	81,
	81,
	81,
	85,
	85,
	89,
	90,
	90,
	60,
	91,
	61,
	92,
	93,
	94,
	95,
	95,
	96,
	97,
	98,
	99,
	100,
	101,
	99,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	81,
	101,
	86,
	80,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
	101,
};

const unsigned int value[199] = {
	0,
	1,
	12,
	13,
	15,
	16,
	18,
	32,
	31,
	35,
	34,
	38,
	37,
	45,
	40,
	42,
	44,
	55,
	46,
	65,
	57,
	61,
	59,
	58,
	60,
	64,
	62,
	63,
	67,
	69,
	66,
	68,
	56,
	6,
	9,
	8,
	5,
	11,
	7,
	10,
	29,
	48,
	50,
	52,
	53,
	54,
	71,
	3,
	4,
	14,
	17,
	19,
	30,
	33,
	36,
	39,
	41,
	47,
	49,
	73,
	43,
	75,
	77,
	78,
	80,
	81,
	83,
	84,
	85,
	87,
	88,
	23,
	25,
	24,
	89,
	90,
	91,
	92,
	20,
	28,
	22,
	21,
	27,
	26,
	94,
	101,
	103,
	51,
	105,
	108,
	110,
	111,
	113,
	112,
	114,
	115,
	117,
	116,
	118,
	106,
	119,
	121,
	122,
	123,
	124,
	125,
	127,
	145,
	147,
	138,
	148,
	151,
	134,
	86,
	135,
	132,
	131,
	133,
	136,
	153,
	143,
	154,
	93,
	139,
	142,
	140,
	141,
	150,
	149,
	155,
	157,
	156,
	104,
	158,
	107,
	159,
	160,
	161,
	162,
	163,
	164,
	165,
	166,
	168,
	169,
	53,
	167,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	144,
	53,
	152,
	137,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
	53,
};


parse_action_t get_action(parse_state_t state, token_type_t token) 
{
    unsigned int i;
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
    int exception;

    lex = &parser->lex;
    str = &lex->buffer;
    filename = parser->filename;
    sstack = &parser->sstack;
    state = CMD0;
    pstack = &parser->pstack;

consume:
    if (state == DONE && sstack->size == 0) {
		pstack_eval_frame(pstack);
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
		pstack_eval_frame(pstack);
		if (sstack->size == 0) {
            return token == TOK_EOF ? 1 : 0;
		}
        state = (unsigned int) int_stack_pop(sstack);
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

 		case CMD4_SYMBOL_SVL0:
			pstack_set_vars_logic(pstack);
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, CMD4a);
			int_stack_push(sstack, TRM0);
			int_stack_push(sstack, SRT0);
			state = SVL0;
			goto consume;

 		case CMD4_WC_ERR_SYM:
			state = ERR_SYM;
			goto skip;

 		case CMD4a_RP_DONE:
			state = DONE;
			goto consume;

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
			pstack_push_string(pstack, str, loc);
			state = CMD8c;
			goto consume;

 		case CMD8c_SYMBOL_CMD8c:
			pstack_push_string(pstack, str, loc);
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

 		case CMD11_SYMBOL_CMD11a:
			pstack_push_string(pstack, str, loc);
			state = CMD11a;
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

 		case CMD11e_SYMBOL_CMD11e:
			pstack_push_string(pstack, str, loc);
			state = CMD11e;
			goto consume;

 		case CMD11e_RP_CMD11f:
			state = CMD11f;
			goto consume;

 		case CMD11f_RP_CMD11a:
			state = CMD11a;
			goto consume;

 		case CMD12_SYMBOL_CMD12a:
			pstack_push_string(pstack, str, loc);
			state = CMD12a;
			goto consume;

 		case CMD12a_KW_INPUT_SVL0:
			pstack_push_attr(pstack, TOK_KW_INPUT, loc);
			pstack_set_vars_input(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_OUTPUT_SVL0:
			pstack_push_attr(pstack, TOK_KW_OUTPUT, loc);
			pstack_set_vars_output(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_LOCAL_SVL0:
			pstack_push_attr(pstack, TOK_KW_LOCAL, loc);
			pstack_set_vars_local(pstack);
			int_stack_push(sstack, CMD12a);
			state = SVL0;
			goto consume;

 		case CMD12a_KW_ASSUMPTION_CMD12b:
			pstack_push_attr(pstack, TOK_KW_ASSUMPTION, loc);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_FAIRNESS_CMD12b:
			pstack_push_attr(pstack, TOK_KW_FAIRNESS, loc);
			state = CMD12b;
			goto consume;

 		case CMD12a_KW_REACHABLE_CMD12c:
			pstack_push_attr(pstack, TOK_KW_REACHABLE, loc);
			state = CMD12c;
			goto consume;

 		case CMD12a_KW_CURRENT_CMD12d:
			pstack_push_attr(pstack, TOK_KW_CURRENT, loc);
			state = CMD12d;
			goto consume;

 		case CMD12a_KW_QUERY_CMD12e:
			pstack_push_attr(pstack, TOK_KW_QUERY, loc);
			state = CMD12e;
			goto consume;

 		case CMD12a_KW_QUERIES_CMD12f:
			pstack_push_attr(pstack, TOK_KW_QUERIES, loc);
			state = CMD12f;
			goto consume;

 		case CMD12a_RP_DONE:
			state = DONE;
			goto consume;

 		case CMD12b_LP_CMD12b0:
			state = CMD12b0;
			goto consume;

 		case CMD12b0_SYMBOL_TRM0nextinput:
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, CMD12b1);
			state = TRM0nextinput;
			goto consume;

 		case CMD12b1_RP_CMD12a:
			state = CMD12a;
			goto consume;

 		case CMD12c_LP_CMD12c0:
			state = CMD12c0;
			goto consume;

 		case CMD12c0_SYMBOL_TRM0next:
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, CMD12c1);
			state = TRM0next;
			goto consume;

 		case CMD12c1_RP_CMD12a:
			state = CMD12a;
			goto consume;

 		case CMD12d_LP_CMD12d0:
			state = CMD12d0;
			goto consume;

 		case CMD12d0_SYMBOL_TRM0:
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, CMD12d1);
			state = TRM0;
			goto consume;

 		case CMD12d1_RP_CMD12a:
			state = CMD12a;
			goto consume;

 		case CMD12e_LP_CMD12e0:
			state = CMD12e0;
			goto consume;

 		case CMD12e0_SYMBOL_CMD12e1:
			pstack_push_string(pstack, str, loc);
			state = CMD12e1;
			goto consume;

 		case CMD12e1_LP_CMD12e2:
			state = CMD12e2;
			goto consume;

 		case CMD12e2_SYMBOL_CMD12e3:
			pstack_push_string(pstack, str, loc);
			state = CMD12e3;
			goto consume;

 		case CMD12e3_SYMBOL_CMD12e3:
			pstack_push_string(pstack, str, loc);
			state = CMD12e3;
			goto consume;

 		case CMD12e3_RP_CMD12e4:
			state = CMD12e4;
			goto consume;

 		case CMD12e4_RP_CMD12a:
			state = CMD12a;
			goto consume;

 		case CMD12f_LP_CMD12f0:
			state = CMD12f0;
			goto consume;

 		case CMD12f0_LP_CMD12f1:
			pstack_push_attr(pstack, TOK_KW_QUERY, loc);
			state = CMD12f1;
			goto consume;

 		case CMD12f1_SYMBOL_CMD12f2:
			pstack_push_string(pstack, str, loc);
			state = CMD12f2;
			goto consume;

 		case CMD12f2_LP_CMD12f3:
			state = CMD12f3;
			goto consume;

 		case CMD12f3_SYMBOL_CMD12f4:
			pstack_push_string(pstack, str, loc);
			state = CMD12f4;
			goto consume;

 		case CMD12f4_SYMBOL_CMD12f4:
			pstack_push_string(pstack, str, loc);
			state = CMD12f4;
			goto consume;

 		case CMD12f4_RP_CMD12f5:
			state = CMD12f5;
			goto consume;

 		case CMD12f5_RP_CMD12f6:
			state = CMD12f6;
			goto consume;

 		case CMD12f6_LP_CMD12f0:
			state = CMD12f0;
			goto skip;

 		case CMD12f6_RP_CMD12a:
			state = CMD12a;
			goto consume;

 		case TRM0nextinput_WC_TRM1:
			pstack_enable_input_next_vars(pstack);
			state = TRM1;
			goto skip;

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
			pstack_push_hex(pstack, str, loc);
			state = DONE;
			goto consume;

 		case TRM1_BINARY_DONE:
			pstack_push_frame(pstack, FRM_TERM, loc);
			pstack_push_binary(pstack, str, loc);
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
			pstack_push_let(pstack, loc);
			state = TRM6;
			goto consume;

 		case TRM2_RW_FORALL_TRM7:
			pstack_push_quantifier(pstack, TOK_RW_FORALL, loc);
			state = TRM7;
			goto consume;

 		case TRM2_RW_EXISTS_TRM7:
			pstack_push_quantifier(pstack, TOK_RW_EXISTS, loc);
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
			pstack_push_frame(pstack, FRM_TERM_BIND, loc);
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, TRM6c);
			state = TRM1;
			goto consume;

 		case TRM6c_RP_DONE:
			int_stack_push(sstack, TRM6d);
			state = DONE;
			goto consume;

 		case TRM6d_LP_TRM6b:
			state = TRM6b;
			goto consume;

 		case TRM6d_RP_TRM1:
			int_stack_push(sstack, TRM6e);
			state = TRM1;
			goto consume;

 		case TRM6e_RP_DONE:
			state = DONE;
			goto consume;

 		case TRM7_LP_SVL0a:
			pstack_set_vars_logic(pstack);
			int_stack_push(sstack, TRM7a);
			int_stack_push(sstack, TRM1);
			state = SVL0a;
			goto skip;

 		case TRM7a_RP_DONE:
			state = DONE;
			goto consume;

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
			pstack_push_frame(pstack, FRM_VAR_DECL, loc);
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

 		case SVL3_RP_DONE:
			int_stack_push(sstack, SVL1);
			state = DONE;
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
			pstack_push_string(pstack, str, loc);
			int_stack_push(sstack, SRT2);
			state = SRT0;
			goto consume;

 		case SRT1_RW_UNDERSCORE_SRT3:
			state = SRT3;
			goto consume;

 		case SRT1_LP_SRT4:
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

