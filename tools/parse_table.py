# Using python3.10

import argparse
import pathlib
import sys
import re

from typing import Optional, NewType, cast

FILE_DIR = pathlib.Path(__file__).parent

"""
We have state/token/state triples. We call a state/token pair an "action". 
The parser includes a stack of states.

The parser uses multiple automata to parse input and uses a stack of states to determine which automata to use at a given time. Initially the parser begins in the "command" automata with an empty stack. The parser computes an action code given the current state/token pair, executes that action's code, sets the next state, then does some stack management. If the current state is "done", this means the current automata is complete. At which point, if the stack is empty, the program is done parsing. Otherwise, we pop the top of the stack off and continue parsing from that state. 

Implementing the parse tables:
For a lazy lookup table, we could allocate an array `lookup` of size NUM_STATES * NUM_TOKENS and do a lookup in a single check such as in `lookup[state][token]`. But in our case we have ~100 states and ~100 tokens, which results in an array of size ~10,000, which is a bit too big for my liking. The fact that we know our full set of states/tokens ahead of time and most state/token pairs are invalid means we can afford to do some stupid computation ahead of time when building the parse tables.

"""

State = NewType("State", str)
Token = NewType("Token", str)
Action = NewType("Action", str)

DEFAULT_ERROR_STATE = State("PS_ERR")
DONE_STATE = State("PS_DONE")
INIT_STATE = State("PS_CMD0")

WILDCARD_TOKEN = Token("*")


def get_action(state: State, token: Token, next: State) -> Action:
    if token == WILDCARD_TOKEN:
        return Action(f"PA_{state[3:]}_WC_{next[3:]}")
    return Action(f"PA_{state[3:]}_{token}_{next[3:]}")


DEFAULT_ERROR_ACTION = get_action(State("PS_ANY"), WILDCARD_TOKEN, DEFAULT_ERROR_STATE)

PARSE_STACK_PUSH_FN = "int_stack_push(state_stack, {state})"

C_PREAMBLE = """
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

"""

C_PARSE_FN = """
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
    if (state ==""" + str(DONE_STATE) + """ && state_stack->top == 0) {
		return 0;
	}

    lexer_next_token(lex);
	token = lex->tok_type;
    lineno = lex->lineno;
    col = lex->col;

skip:
    if (state == """ + str(DEFAULT_ERROR_STATE) + """) {
        print_error_with_loc(filename, lineno, col, "syntax error");
        return 1;
    } 
    
    if (state == """ + str(DONE_STATE) + """) {
        if (state_stack->top == 0) {
            return 0;
        }
        state = int_stack_pop(state_stack);
        // Then we handle the top frame of the parse stack
    }

    action = get_action(state, token);

#ifdef DEBUG_PARSER
    fprintf(stderr, "state: %d, token: '%s' (%d), action: %d\\n", state, token_type_str[token], token, action);
#endif

    switch(action) {
"""


def parse_tokens(token_h: str) -> list[Token]:
    """Collects and returns tokens from token.h"""
    tokens = []

    for line in token_h.splitlines():
        re_match = re.match(r"    TOK_[A-Z_]+,", line)
        if not re_match:
            continue

        token = re_match.group()[:-1].strip()
        tokens.append(token)

    return tokens


def parse_table(content: str, tokens: list[Token]):
    table: dict[tuple[State, Token], tuple[State, bool, Optional[list[State]]]] = {}
    states: list[State] = [DEFAULT_ERROR_STATE, DONE_STATE]
    actions: list[Action] = [DEFAULT_ERROR_ACTION]
    edges: dict[State, list[Token]] = {DEFAULT_ERROR_STATE: [], DONE_STATE: []}
    default: dict[State, Action] = {}

    for line in content.splitlines():
        if line[0:2] == "//":
            continue
        line_data = line.split()
        if len(line_data) == 0:
            continue
        if len(line_data) != 5:
            print(sys.stderr, f"warning: ignoring bad line ({line})")
            continue

        (state, token, next, consume, push) = line_data
        state = State("PS_" + state)
        token = Token(token)
        next = State("PS_" + next)

        if (state, token) in table:
            print(sys.stderr, f"error: repeated state/token pair ({state}, {token})")

        if token not in tokens and token != WILDCARD_TOKEN:
            print(sys.stderr, f"error: token not in token set ({token})")

        if push == "_":
            push = None
        else:
            push = [State("PS_" + p) for p in push.split(",")]

        if consume == "consume":
            consume = True
        else:
            consume = False

        action = get_action(state, token, next)
        table[(state, token)] = (next, consume, push)
        if state not in states:
            states.append(state)
        if next not in states:
            states.append(next)
        actions.append(action)
        if state not in edges:
            edges[state] = []
        if next not in edges:
            edges[next] = []

        if token != WILDCARD_TOKEN:
            edges[state].append(token)
            continue

        if state in default:
            print(f"error: set default for state twice ({state})", sys.stderr)
            continue
        default[state] = action

    for state in [s for s in states if s not in default]:
        default[state] = DEFAULT_ERROR_ACTION

    states.sort()
    actions.sort()

    return (table, states, actions, edges, default)


def pp_array(values: list[str]) -> str:
    max_elem_width = max([len(v) for v in values])
    max_row_char_length = 76  # 80 chars minus 4 for tab
    actual_elem_width = max_elem_width + 2  # chars for ', '
    elems_per_row = int(max_row_char_length / actual_elem_width)

    pp = "\t"
    num_rows = int(len(values) / elems_per_row) + 1

    for i in range(0, num_rows):
        start = i * (elems_per_row)
        end = min((i + 1) * (elems_per_row), len(values))
        pp += " ".join(
            ["{v:{e}}".format(v=v+",", e=max_elem_width) for v in values[start:end]]
        )
        pp += "\n\t"

    return pp.rstrip()[:-1]


def find_base(
    edges: list[Token],
    check: dict[int, State],
    tokens: list[Token],
) -> int:
    """Given a state with a set of outgoing edges with labels in `edges`, returns the lowest index `i` such that for all `t` in `edges`, `check[i+t]` is empty."""
    i = 0
    while any([(tokens.index(tok) + i in check) for tok in edges]):
        i += 1
    return i


def gen_states(states: list[State]) -> str:
    return (
        "typedef enum parse_state {\n"
        + pp_array([str(s) for s in states])
        + "\n} parse_state_t;\n\n"
    )


def gen_actions(actions: list[Action]) -> str:
    return (
        "typedef enum parse_action {\n"
        + pp_array([str(a) for a in actions])
        + "\n} parse_action_t;\n\n"
    )


def gen_base(states: list[State], base: dict[State, int]) -> str:
    base_array = [-1 for _ in range(0, len(states))]
    for i in range(0, len(states)):
        base_array[i] = base[states[i]]

    if any([b == -1 for b in base_array]):
        print("error: did not set base for some value", file=sys.stderr)
        print(base_array, file=sys.stderr)

    return (
        "const int base["
        + str(len(base_array))
        + "] = {\n"
        + pp_array([str(b) for b in base_array])
        + "\n};\n\n"
    )


def gen_default(states: list[State], default: dict[State, Action]) -> str:
    default_array = [DEFAULT_ERROR_ACTION for _ in range(0, len(states))]
    for i in range(0, len(states)):
        default_array[i] = default[states[i]]

    return (
        "const int def["
        + str(len(default_array))
        + "] = {\n"
        + pp_array([str(d) for d in default_array])
        + "\n};\n\n"
    )


def gen_check(
    states: list[State],
    base: dict[State, int],
    edges: dict[State, list[Token]],
) -> str:
    max_base = max([b for b in base.values()])
    table_size = max_base + len(tokens)

    # default is an int that no state will be equal to (len(states))
    check_array = [len(states) for _ in range(0, table_size)]

    for state in states:
        for token in edges[state]:
            b = base[state]
            offset = tokens.index(token)
            check_array[b + offset] = states.index(state)

    return (
        "const int check["
        + str(len(check_array))
        + "] = {\n"
        + pp_array([str(b) for b in check_array])
        + "\n};\n\n"
    )


def gen_value(
    states: list[State],
    actions: list[Action],
    table: dict[tuple[State, Token], tuple[State, bool, Optional[list[State]]]],
    base: dict[State, int],
    edges: dict[State, list[Token]],
) -> str:
    max_base = max([b for b in base.values()])
    table_size = max_base + len(tokens)

    # default is go to error state
    value_array = [states.index(DEFAULT_ERROR_STATE) for _ in range(0, table_size)]

    for state in states:
        for token in edges[state]:
            b = base[state]
            offset = tokens.index(token)
            (next, _, _) = table[(state, token)]
            value_array[b + offset] = actions.index(get_action(state, token, next))

    return (
        "const int value["
        + str(len(value_array))
        + "] = {\n"
        + pp_array([str(b) for b in value_array])
        + "\n};\n\n"
    )


def gen_table(content: str, tokens: list[Token]) -> str:
    (table, states, actions, edges, default) = parse_table(content, tokens)

    c_prog = ""
    c_prog += gen_states(states)
    c_prog += gen_actions(actions)

    base: dict[State, int] = {}
    check: dict[int, State] = {}

    for state in states:
        b = find_base(edges[state], check, tokens)
        base[state] = b
        for token in edges[state]:
            offset = tokens.index(token)
            check[b + offset] = state

    c_prog += gen_default(states, default)
    c_prog += gen_base(states, base)
    c_prog += gen_check(states, base, edges)
    c_prog += gen_value(states, actions, table, base, edges)

    cases = []
    for (state, token), (next, consume, push) in table.items():
        token = cast(Token, token)  # pylance giving me a type warning?
        code = f"\t\tcase {get_action(state, token, next)}:\n"
        if push:
            push = cast(list[str], push)
            for p in push:
                code += f"\t\t\t{PARSE_STACK_PUSH_FN.format(state=p)};\n"
        code += f"\t\t\tstate = {next};\n"
        if consume:
            code += "\t\t\tgoto consume;\n"
        else:
            code += "\t\t\tgoto skip;\n"
        code += "\n"
        cases.append(code)

    error_case = (
        f"\t\tcase {DEFAULT_ERROR_ACTION}:\n"
        + f"\t\t\tstate = {DEFAULT_ERROR_STATE};\n"
        + "\t\t\tgoto skip;\n\n"
    )
    cases.append(error_case)

    print(C_PREAMBLE + c_prog + C_PARSE_FN + " ".join(cases) + "\t}\n\n\treturn 1;\n}")

    return ""


if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("input", help="path to parse table file")
    arg_parser.add_argument(
        "--token_h",
        default=f"{FILE_DIR.parent}/src/parse/token.h",
        help="path to token.h",
    )
    args = arg_parser.parse_args()

    token_h_path = pathlib.Path(args.token_h)
    if not token_h_path.is_file():
        print(f"error: token.h file is invalid ({token_h_path})", file=sys.stderr)
        sys.exit(1)

    with open(token_h_path, "r") as f:
        tokens = parse_tokens(f.read())

    parse_tbl_path = pathlib.Path(args.input)
    if not parse_tbl_path.is_file():
        print(f"error: parse table file is invalid ({parse_tbl_path})", file=sys.stderr)
        sys.exit(1)

    with open(parse_tbl_path, "r") as f:
        output = gen_table(f.read(), tokens)

    print(output)
