CC := gcc
GPERF := gperf
PYTHON := python3

TOOLS_DIR := tools
SRC_DIR := src
OBJ_DIR := obj
BIN := moxisc

DBGFLAGS := -g -O0 -fdata-sections -ffunction-sections -fno-common -fsanitize=undefined -fsanitize=address -pedantic -Waggregate-return -Wall -Wbad-function-cast -Wcast-align -Wcast-qual -Wconversion -Wdisabled-optimization -Wdouble-promotion -Wduplicated-branches -Wduplicated-cond -Wextra -Wfloat-equal -Wformat-nonliteral -Wformat-security -Wformat-truncation -Wformat-y2k -Wformat=2 -Wimplicit -Wimport -Winit-self -Winline -Winvalid-pch -Wlogical-op -Wlong-long -Wmisleading-indentation -Wmissing-declarations -Wmissing-field-initializers -Wmissing-format-attribute -Wmissing-include-dirs -Wmissing-noreturn -Wmissing-prototypes -Wnested-externs -Wnull-dereference -Wodr -Wpacked -Wpedantic -Wpointer-arith -Wredundant-decls -Wshadow -Wsign-conversion -Wstack-protector -Wstrict-aliasing=2 -Wstrict-overflow=5 -Wstrict-prototypes -Wswitch-default -Wundef -Wundef -Wunreachable-code -Wunused -Wunused-parameter -Wvariadic-macros -Wwrite-strings -Wall -Wextra -pedantic -Wshadow -Wpointer-arith -Wcast-qual -Wstrict-prototypes -Wmissing-prototypes -Wno-switch-enum -Wno-unknown-warning-option -Wno-gnu-binary-literal --coverage

CPPFLAGS := 
CFLAGS := -Wall -I$(SRC_DIR) -I/usr/local/include $(CPPFLAGS) -DDEBUG_PARSER -g

LIB :=

# Token hashing
gperf_generated := $(SRC_DIR)/parse/hash_token.h \
				   $(SRC_DIR)/parse/hash_symbol.h

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
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_token.h --lookup-function-name=in_moxi_tok \
		--hash-function=hash_tok $(SRC_DIR)/parse/token.gperf

$(SRC_DIR)/parse/hash_symbol.h: $(SRC_DIR)/parse/symbol.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_symbol.h --lookup-function-name=in_moxi_sym \
		--hash-function=hash_sym $(SRC_DIR)/parse/symbol.gperf

$(SRC_DIR)/parse/parse.c: $(TOOLS_DIR)/moxi.tbl $(TOOLS_DIR)/parse_table.py
	$(PYTHON) $(TOOLS_DIR)/parse_table.py $(TOOLS_DIR)/moxi.tbl > $(SRC_DIR)/parse/parse.c

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJ_DIR)/%.d: $(SRC_DIR)/%.c | $(OBJ_DIR)
	@set -e; rm -f $@; echo Building dependency file $@ ; \
		$(CC) -MM -MG -MT $*.o $(CFLAGS) $(CPPFLAGS) $< > $@.$$$$ ; \
		sed 's,\($*\).o[ :]*,$(OBJ_DIR)/\1.o $@ : ,g' < $@.$$$$ > $@ ; \
		sed 's, \($*\).h, $(SRC_DIR)/\1.h,g' < $@.$$$$ > $@ ; \
		rm -f $@.$$$$

ifneq ($(MAKECMDGOALS),clean)
include $(DEP_FILES)
endif

$(BIN): $(gperf_generated) $(OBJ_FILES) $(DEP_FILES)
	$(CC) $(CFLAGS) -o $@ $(OBJ_FILES) $(LIB)

$(OBJ_DIR):
	mkdir -p $(OBJ_DIRS)

bin: $(BIN)

clean:
	rm -rf $(OBJ_DIR) $(BIN) $(gperf_generated) $(python_generated)

	