CC := gcc
GPERF := gperf
PYTHON := python3

TOOLS_DIR := tools
SRC_DIR := src
OBJ_DIR := obj
BIN := moxisc

CFLAGS := -Wall -I$(SRC_DIR)

# Token hashing
gperf_generated := $(SRC_DIR)/parse/hash_token.h \
				   $(SRC_DIR)/parse/hash_symbol.h

# Parser generation
python_generated := $(SRC_DIR)/parse/parser.c

SRC_DIRS := \
	$(SRC_DIR) \
	$(SRC_DIR)/parse \
	$(SRC_DIR)/util \
	$(SRC_DIR)/io
INC_DIRS := $(SRC_DIRS)
OBJ_DIRS := $(OBJ_DIR) $(addprefix $(OBJ_DIR), $(subst $(SRC_DIR),,$(SRC_DIRS)))

SRC_FILES := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*))) $(python_generated)
OBJ_FILES := $(addprefix $(OBJ_DIR)/, $(addsuffix .o, $(basename $(subst $(SRC_DIR)/,,$(SRC_FILES)))))

# Define default rule first
default: $(BIN)

$(SRC_DIR)/parse/hash_token.h: $(SRC_DIR)/parse/gperf/token.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_token.h --lookup-function-name=in_moxi_tok \
		--hash-function=hash_tok $(SRC_DIR)/parse/gperf/token.gperf

$(SRC_DIR)/parse/hash_symbol.h: $(SRC_DIR)/parse/gperf/symbol.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_symbol.h --lookup-function-name=in_moxi_sym \
		--hash-function=hash_sym $(SRC_DIR)/parse/gperf/symbol.gperf

$(SRC_DIR)/parse/parser.c: $(TOOLS_DIR)/moxi.tbl $(TOOLS_DIR)/parse_table.py
	$(PYTHON) $(TOOLS_DIR)/parse_table.py $(TOOLS_DIR)/moxi.tbl > $(SRC_DIR)/parse/parser.c

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

$(BIN): $(gperf_generated) $(python_generated) $(OBJ_FILES)
	$(CC) $(CFLAGS) -o $@ $(OBJ_FILES)

$(OBJ_DIR):
	mkdir -p $(OBJ_DIRS)

bin: $(BIN)

clean:
	rm -rf $(OBJ_DIR) $(BIN) $(gperf_generated) $(python_generated)

	