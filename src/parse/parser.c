#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "moxi/commands.h"
#include "parse/parse_error.h"
#include "parse/parser.h"


/**
 * 
*/
void init_parser(parser_t *parser, const char *filename)
{
    init_lexer(&parser->lex, filename);
    parser->depth = 0;
}


/**
 * 
*/
void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
}


/**
 * 
*/



/**
 * Pushes a sort, variable, or function onto the stack depending on the parser's context. The
 * current token should be a symbol.
*/
token_type_t parse_symbol(parser_t *parser)
{
    lexer_t *lex;
    string_buffer_t *buffer;
    symbol_table_t *symbol_table;
    context_t *context;
    parse_stack_t *stack;
    token_type_t token_type;
    char *symbol;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    stack = &parser->stack;
    symbol_table = &context->symbol_table;
    symbol = lex->buffer.data;

    symbol_kind_t symbol_kind;
    symbol_kind = symbol_table_find(symbol_table, symbol);

    parse_stack_push_symbol(stack, symbol);
    parse_stack_new_frame(stack);
    
    switch (symbol_kind)
    {
    case MOXI_SYM_KIND_SORT:
        parse_stack_process_sort(stack, context);
        break;

    case MOXI_SYM_KIND_FUNCTION:
        parse_stack_process_function(stack, context);
        break;
    
    case MOXI_SYM_KIND_VARIABLE:
        parse_stack_process_variable(stack, context);
        break;
    
    case MOXI_SYM_KIND_SYSTEM:
        // parse_stack_process_system(stack, context);
        break;
    
    default:
        parse_stack_process_error(stack, PARSE_ERROR_EXPECTED_SYMBOL, 
            lex->loc.lineno, lex->loc.col, "unrecognized symbol '%s'", symbol);
        break;
    }
}


/**
 * Iterates the lexer to the next token, pushing an error onto the stack if the token type is not
 * `expect`.
*/
void parse_token(parser_t *parser, token_type_t expect)
{
    lexer_t *lex;
    token_type_t token_type;
    error_stack_t *error;

    lex = &parser->lex;
    error = &parser->error_stack;

    token_type = lexer_next_token(lex);

    if (token_type != expect) {
        push_error(error, PARSE_ERROR_EXPECTED_RP, 
            lex->loc.lineno, lex->loc.col, "expected '%s'", token_type_str[expect]);
    }
}


/**
 * The current token should be a symbol or `(`. Pushes a sort, variable, or function onto the stack
 * depending on the parser's context and indices. Pushes an error onto the stack otherwise and
 * consumes until `)` or EOF.
 * 
 * `symbol`
 * `(_ <symbol> <symbol-or-int-list>)`
*/
void parse_identifier(parser_t *parser)
{
    lexer_t *lex;
    symbol_table_t *symbol_table;
    parse_stack_t *stack;
    context_t *context;
    token_type_t token_type;
    char *symbol;
    uint64_t value;

    lex = &parser->lex;
    stack = &parser->stack;
    context = &parser->context;
    token_type = lex->tok_type;

    if (token_type == MOXI_TOK_SYMBOL) {
        parse_symbol(parser);
        return;
    }

    parse_token(parser, MOXI_TOK_LP);
    parse_stack_new_frame(stack);
    parse_token(parser, MOXI_TOK_RW_UNDERSCORE);
    parse_symbol(parser);

    token_type = lexer_next_token(lex);
    while(token_type != MOXI_TOK_RP) {
        switch (token_type)
        {
        case MOXI_TOK_SYMBOL:
            symbol = lex->buffer.data;
            parse_stack_push_symbol(stack, symbol);
            break;

        case MOXI_TOK_NUMERAL:
            symbol = lex->buffer.data;
            value = strtol(symbol, NULL, 10); // FIXME: This only goes up to 64 bits
            parse_stack_push_numeral(stack, value);
            break;

        default:
            push_parse_error(stack, PARSE_ERROR_EXPECTED_SYMBOL, 
                lex->loc.lineno, lex->loc.col, "expected symbol, numeral, or ')'");
            break;
        }

        token_type = lexer_next_token(lex);
    }

    // Check indexed identifier and push onto stack

    /**
     * Indexed identifiers:
     * (_ BitVec <numeral>)
     * (_ extract <numeral> <numeral>)
     * (_ repeat <numeral>)
     * (_ zero_extend <numeral>)
     * (_ sign_extend <numeral>)
     * (_ rotate_right <numeral>)
     * (_ rotate_left <numeral>)
    */

    parse_stack_pop_frame(stack);

    // Consume trailing ')'
    parse_token(parser, MOXI_TOK_RP);   
}


/**
 * Parses a (potentially empty) list of sort binders, pushing each binder to the parse stack.
 * 
 * `( (<var-symbol> <sort-symbol>)* )`
*/
void parse_sort_binder_list(parser_t *parser)
{
    lexer_t *lex;
    token_type_t token_type;
    parse_stack_t *stack;
    context_t *context;
    uint32_t lineno, col;
    parse_stack_elem_t elem;

    lex = &parser->lex;
    stack = &parser->stack;
    context = &parser->context;

    parse_token(parser, MOXI_TOK_LP);
    token_type = lexer_next_token(lex);

    while(token_type == MOXI_TOK_LP) {
        // Current state:
        // `( <var-symbol> <sort-symbol> )`
        //  ^
        parse_token(parser, MOXI_TOK_LP);
        parse_symbol(parser);
        parse_identifier(parser);
        parse_token(parser, MOXI_TOK_RP);

        // Check the validity of the var and sort



        token_type = lexer_next_token(lex);
    }

    parse_token(parser, MOXI_TOK_RP);
}


/**
 * When we see an open parentheses, we push the following identifier onto the parse stack as the
 * beginning of a new scope. When we see a close parentheses, we pop the top frame from the stack
 * and perform a sort check.
 * 
 * `<symbol>`
 * `(_ <symbol> <symbol-or-int-list>)` (identifier)
 * `(<identifier> <term>*)`
*/
term_t *parse_term(parser_t *parser)
{
    lexer_t *lex;
    token_type_t token_type;
    parse_stack_t *stack;
    context_t *context;
    uint32_t depth; // Number of nested parens -- stop parsing once this reaches 0 after a `)` token

    depth = 0;
    token_type = lexer_next_token(lex);

    do {
        switch (token_type)
        {
        case MOXI_TOK_BINARY:
            // parse_binary(parser);

        case MOXI_TOK_HEX:
            // parse_hex(parser);

        case MOXI_TOK_DECIMAL:
            // parse_decimal(parser);
        
        case MOXI_TOK_SYMBOL:
            parse_symbol(parser);
            break;

        case MOXI_TOK_LP:
            parse_stack_new_frame(stack);
            token_type = lexer_next_token(lex);

            if (token_type == MOXI_TOK_LP) {
                // `((_ ...) ...)`
                //   ^
                // Iterate since `parse_identifier` expects current token to be `_` or symbol
                lexer_next_token(lex);
            }

            parse_identifier(parser);
            depth++;

            break;
        
        case MOXI_TOK_RP:
            // check and pop top frame, push result back onto stack
            process_table[stack->data[stack->top_frame].tag](stack, context);
            parse_stack_pop_frame(stack);
            depth--;
            break;

        default:
            push_error(stack, 0, 0, 0, "expected symbol, '(', or ')'");
            break;
        }
    } while(depth > 0);

}


/**
 * Parse a `define-fun` MoXI command. The current token should be `define-fun`.
 *
 * `(define-fun <fresh-symbol> <binder-list> <sort-symbol> <term>)`
*/
void parse_define_fun(parser_t *parser) 
{
    lexer_t *lex;
    string_buffer_t *buffer;
    context_t *context;
    token_type_t token_type;

    char *function_symbol;
    string_pair_list_t *rank;
    term_t *term;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    context = &parser->context;

    function_symbol = parse_symbol(parser);
    parse_sort_binder_list(parser);
    parse_sort(parser);

    // open scope


    term = parse_term(parser);
} 


/**
 * Parse a `define-sort` MoXI command. The current token should be `define-sort`. 
 * 
 * FIXME: Consider adding some "alias" table, since that's what these really are -- but how does
 * this relate to defined functions?
 * 
 * Examples: 
 * - `(define-sort BV8 () (_ BitVec 8))`
 * - `(define-sort BV8IdxArray (ElemSort) (Array BV8 ElemSort))`
 *
 * `define-sort <fresh-symbol> <sort-symbol-list> <sort>`
*/
void parse_define_sort(parser_t *parser) 
{

} 



int parse_moxi(parser_t *parser)
{
    lexer_t *lex;
    parse_stack_t *stack;
    error_stack_t *errors;
    token_type_t token_type;

    lex = &parser->lex;
    stack = &parser->stack;

    do {
        parse_left_paren(parser);

        token_type = lexer_next_token(lex);

        switch (token_type)
        {
        case MOXI_TOK_RW_DEFINE_SYS:
        case MOXI_TOK_RW_CHECK_SYS:
        case MOXI_TOK_RW_DECLARE_SORT:
        case MOXI_TOK_RW_DECLARE_ENUM_SORT:
        case MOXI_TOK_RW_DECLARE_CONST:
        case MOXI_TOK_RW_DECLARE_FUN:
        case MOXI_TOK_RW_DEFINE_SORT:
        case MOXI_TOK_RW_DEFINE_CONST:
        case MOXI_TOK_RW_DEFINE_FUN:
            parse_define_fun(parser);
            break;

        case MOXI_TOK_RW_EXIT:
        case MOXI_TOK_RW_SET_LOGIC:
        case MOXI_TOK_RW_ECHO:
        default:
            break;
        }

        parse_right_paren(parser);

        if (errors->num_errors == 0) {
            moxi_check_fun[parser->command.type]();
            moxi_execute_fun[parser->command.type]();
        }

    } while(token_type != MOXI_TOK_EOF);

    return -1;
}

