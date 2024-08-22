# Using python3.10

import argparse
import pathlib
import sys
import re

from typing import Optional, NewType, cast

FILE_DIR = pathlib.Path(__file__).parent
TOKEN_H_PATH = FILE_DIR.parent / "src" / "parse" / "token.h"

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

WILDCARD_TOKEN = Token("*")


def get_action(state: State, token: Token, next: State) -> Action:
    if token == WILDCARD_TOKEN:
        return Action(f"{state}_WC_{next}")
    token_name = str(token).replace("TOK_", "")
    return Action(f"{state}_{token_name}_{next}")


DEFAULT_ERROR_STATE = State("ERR")
DONE_STATE = State("DONE")
INIT_STATE = State("CMD0")


DEFAULT_ERROR_ACTION = get_action(
    DEFAULT_ERROR_STATE, WILDCARD_TOKEN, DEFAULT_ERROR_STATE
)

PARSE_STACK_PUSH_FN = "int_stack_push(sstack, {state})"

C_PREAMBLE = """
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "parse/parse.h"

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

    init_int_stack(&parser->sstack);
    init_pstack(&parser->pstack);
	parser->filename = filename;
	return 0;
}

void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
    delete_int_stack(&parser->sstack);
    delete_pstack(&parser->pstack);
}

"""

C_PARSE_FN = (
    """
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
    string_buffer_t *str;
    const char *filename;
    token_type_t token;
    int_stack_t *sstack;
    parse_state_t state;
    parse_action_t action;
    uint64_t lineno;
    uint64_t col;
    pstack_t *pstack;
    context_t *ctx;

    lex = &parser->lex;
    str = &lex->buffer;
    filename = parser->filename;
    sstack = &parser->sstack;
    state = """
    + str(INIT_STATE)
    + """;
    pstack = &parser->pstack;
    ctx = &parser->ctx;

consume:
    if (state == """
    + str(DONE_STATE)
    + """ && sstack->top == 0) {
		return token == TOK_EOF ? 1 : 0;
	}

    lexer_next_token(lex);
	token = lex->tok_type;
    lineno = lex->lineno;
    col = lex->col;

skip:
    if (state == """
    + str(DEFAULT_ERROR_STATE)
    + """) {
        return 1;
    } 
    
    if (state == """
    + str(DONE_STATE)
    + """) {
        if (sstack->top == 0) {
            return token == TOK_EOF ? 1 : 0;
        }
        state = int_stack_pop(sstack);
        pstack_eval_frame(pstack, ctx);
    }

    if (pstack->status) {
        print_error("type check error");
		int tmp = pstack->status;
        pstack_reset(pstack);
        return tmp;
    }

    action = get_action(state, token);

#ifdef DEBUG_PARSER
    fprintf(stderr, "state: %d, token: '%s' (%d), action: %d\\n", 
        state, token_type_str[token], token, action);
#endif

    switch(action) {
"""
)


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
    table: dict[
        tuple[State, Token], tuple[State, bool, Optional[list[State]], Optional[str]]
    ] = {}
    states: list[State] = [DEFAULT_ERROR_STATE, DONE_STATE]
    actions: list[Action] = [DEFAULT_ERROR_ACTION]
    edges: dict[State, list[Token]] = {DEFAULT_ERROR_STATE: [], DONE_STATE: []}
    default: dict[State, Action] = {}

    for line in content.splitlines():
        if line[0:2] == "//":
            continue
        line_data = line.split(maxsplit=5)
        if len(line_data) == 0:
            continue

        if len(line_data) == 5:
            (state, token, next, consume, push) = line_data
            code = None
        elif len(line_data) == 6:
            (state, token, next, consume, push, code) = line_data
            code = code.strip()[1:-2]
        else:
            print(f"warning: bad line\n\t{line}", file=sys.stderr)
            continue

        state = State(state)
        token = Token(token)
        next = State(next)

        if (state, token) in table:
            print(sys.stderr, f"error: repeated state/token pair ({state}, {token})")

        if token not in tokens and token != WILDCARD_TOKEN:
            print(sys.stderr, f"error: token not in token set ({token})")

        if push == "_":
            push = None
        else:
            push = [State(p) for p in push.split(",")]

        if consume == "consume":
            consume = True
        else:
            consume = False

        action = get_action(state, token, next)
        table[(state, token)] = (next, consume, push, code)
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
        + "\n\t".join([str(s) + "," for s in states])
        + "\n} parse_state_t;\n\n"
    )


def gen_actions(actions: list[Action]) -> str:
    return (
        "typedef enum parse_action {\n"
        + "\n\t".join([str(a) + "," for a in actions])
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
        + "\n\t".join([str(b) + "," for b in base_array])
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
        + "\n\t".join([str(d) + "," for d in default_array])
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
        + "\n\t".join([str(b) + "," for b in check_array])
        + "\n};\n\n"
    )


def gen_value(
    states: list[State],
    actions: list[Action],
    table: dict[
        tuple[State, Token], tuple[State, bool, Optional[list[State]], Optional[str]]
    ],
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
            (next, _, _, _) = table[(state, token)]
            value_array[b + offset] = actions.index(get_action(state, token, next))

    return (
        "const int value["
        + str(len(value_array))
        + "] = {\n"
        + "\n\t".join([str(b) + "," for b in value_array])
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
    for (state, token), (next, consume, push, extra_code) in table.items():
        token = cast(Token, token)  # pylance giving me a type warning?
        code = f"\t\tcase {get_action(state, token, next)}:\n"

        if extra_code:
            code += "".join(
                [
                    "\t\t\t" + line.strip() + ";\n"
                    for line in extra_code.split(";")
                    if not len(line) == 0 and not line.isspace()
                ]
            )

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
        + "\t\t\tprint_error_with_loc(filename, lineno, col, \"syntax error\");\n"
        + f"\t\t\tstate = {DEFAULT_ERROR_STATE};\n"
        + "\t\t\tgoto skip;\n\n"
    )
    cases.append(error_case)

    print(C_PREAMBLE + c_prog + C_PARSE_FN + " ".join(cases) + "\t}\n\n\treturn 1;\n}")

    return ""


if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("input", help="path to parse table file")
    args = arg_parser.parse_args()

    if not TOKEN_H_PATH.is_file():
        print(f"error: token.h file is invalid ({TOKEN_H_PATH})", file=sys.stderr)
        sys.exit(1)

    with open(TOKEN_H_PATH, "r") as f:
        tokens = parse_tokens(f.read())

    parse_tbl_path = pathlib.Path(args.input)
    if not parse_tbl_path.is_file():
        print(f"error: parse table file is invalid ({parse_tbl_path})", file=sys.stderr)
        sys.exit(1)

    with open(parse_tbl_path, "r") as f:
        output = gen_table(f.read(), tokens)

    print(output)
