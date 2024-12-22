CC := clang
GPERF := gperf
PYTHON := python3

TOOLS_DIR := tools
SRC_DIR := src
OBJ_DIR := obj
BIN := moxisc

DBGFLAGS := -g -O0 -DDEBUG -DDEBUG_PARSER -DDEBUG_PSTACK -fsanitize=undefined -fsanitize=address -Waggregate-return -Wbad-function-cast -Wcast-align -Wconversion -Wdisabled-optimization -Wdouble-promotion -Wfloat-equal -Wformat-nonliteral -Wformat-security -Wformat=2 -Wimplicit -Wlong-long -Wmisleading-indentation  -Wmissing-include-dirs -Wpacked -Wpedantic -Wshadow -Wsign-conversion  -Wswitch-default -Wundef -Wunreachable-code -Wunused -Wvariadic-macros -Wwrite-strings -Wall -Wextra -pedantic  -Wpointer-arith -Wcast-qual  -Wno-deprecated-non-prototype

CFLAGS := -Wall -I$(SRC_DIR) -I/usr/local/include -std=c99 

LIB := -lyices

# Token hashing
gperf_generated := $(SRC_DIR)/parse/hash_token.h \
				   $(SRC_DIR)/parse/hash_symbol.h \
				   $(SRC_DIR)/moxi/hash_logic.h

# Parser generation
python_generated := $(SRC_DIR)/parse/parse.c

SRC_DIRS := \
	$(SRC_DIR) \
	$(SRC_DIR)/parse \
	$(SRC_DIR)/util \
	$(SRC_DIR)/moxi \
	$(SRC_DIR)/io
INC_DIRS := $(SRC_DIRS)
OBJ_DIRS := $(OBJ_DIR) $(addprefix $(OBJ_DIR), $(subst $(SRC_DIR),,$(SRC_DIRS)))

ifneq ("$(wildcard $(python_generated))","")
SRC_FILES := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*)))
else
SRC_FILES := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*))) $(python_generated)
endif

OBJ_FILES := $(addprefix $(OBJ_DIR)/, $(addsuffix .o, $(basename $(subst $(SRC_DIR)/,,$(SRC_FILES)))))
DEP_FILES := $(addprefix $(OBJ_DIR)/, $(addsuffix .d, $(basename $(subst $(SRC_DIR)/,,$(SRC_FILES)))))

# Define default rule first
default: $(BIN)

$(SRC_DIR)/parse/hash_token.h: $(SRC_DIR)/parse/token.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_token.h \
		--lookup-function-name=find_moxi_tok \
		--hash-function=hash_tok $(SRC_DIR)/parse/token.gperf

$(SRC_DIR)/parse/hash_symbol.h: $(SRC_DIR)/parse/symbol.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_symbol.h \
		--lookup-function-name=find_moxi_thy_sym \
		--hash-function=hash_sym $(SRC_DIR)/parse/symbol.gperf

$(SRC_DIR)/moxi/hash_logic.h: $(SRC_DIR)/moxi/logic.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/moxi/hash_logic.h \
	 --lookup-function-name=find_moxi_logic \
		--hash-function=hash_logic $(SRC_DIR)/moxi/logic.gperf

$(SRC_DIR)/parse/parse.c: $(TOOLS_DIR)/moxi.tbl $(TOOLS_DIR)/parse_table.py
	$(PYTHON) $(TOOLS_DIR)/parse_table.py $(TOOLS_DIR)/moxi.tbl > $(SRC_DIR)/parse/parse.c

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJ_DIR)/%.d: $(SRC_DIR)/%.c | $(OBJ_DIR)
	@set -e; rm -f $@; echo Building dependency file $@ ; \
		$(CC) -MM -MG -MT $*.o $(CFLAGS) $< > $@.$$$$ ; \
		sed 's,\($*\).o[ :]*,$(OBJ_DIR)/\1.o $@ : ,g' < $@.$$$$ > $@ ; \
		sed 's, \($*\).h, $(SRC_DIR)/\1.h,g' < $@.$$$$ > $@ ; \
		rm -f $@.$$$$

ifneq ($(MAKECMDGOALS),clean)
include $(DEP_FILES)
endif

$(BIN): $(gperf_generated) $(OBJ_FILES) $(DEP_FILES)
	$(CC) -g $(CFLAGS) -o $@ $(OBJ_FILES) $(LIB)

$(OBJ_DIR):
	mkdir -p $(OBJ_DIRS)

bin: $(BIN)

debug: CFLAGS += $(DBGFLAGS)
debug: $(BIN)

clean:
	rm -rf $(OBJ_DIR) $(BIN) $(gperf_generated) $(python_generated)

	