CC := gcc
GPERF := gperf

SRC_DIR := src
OBJ_DIR := obj
BIN := moximc

CFLAGS += -Wall -I$(SRC_DIR) 

SRC_DIRS := \
	$(SRC_DIR) \
	$(SRC_DIR)/parse \
	$(SRC_DIR)/util \
	$(SRC_DIR)/io
INC_DIRS := $(SRC_DIRS)
OBJ_DIRS := $(OBJ_DIR) $(addprefix $(OBJ_DIR), $(subst $(SRC_DIR),,$(SRC_DIRS)))

SRC_FILES := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*)))
OBJ_FILES := $(addprefix $(OBJ_DIR)/, $(addsuffix .o, $(basename $(subst $(SRC_DIR)/,,$(SRC_FILES)))))


# Define default rule first
default: $(BIN)


# Token hashing
gperf_generated := $(SRC_DIR)/parse/hash_keyword.h \
				   $(SRC_DIR)/parse/hash_reserved.h \
				   $(SRC_DIR)/parse/hash_symbol.h

$(SRC_DIR)/parse/hash_keyword.h: $(SRC_DIR)/parse/gperf/keyword.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_keyword.h --lookup-function-name=in_moxi_kw \
		--hash-function=hash_kw $(SRC_DIR)/parse/gperf/keyword.gperf

$(SRC_DIR)/parse/hash_reserved.h: $(SRC_DIR)/parse/gperf/reserved.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_reserved.h --lookup-function-name=in_moxi_rw \
		--hash-function=hash_rw $(SRC_DIR)/parse/gperf/reserved.gperf

$(SRC_DIR)/parse/hash_symbol.h: $(SRC_DIR)/parse/gperf/symbol.gperf
	$(GPERF) -C -E -t --output-file=$(SRC_DIR)/parse/hash_symbol.h --lookup-function-name=in_moxi_sym \
		--hash-function=hash_sym $(SRC_DIR)/parse/gperf/symbol.gperf
		

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

$(BIN): $(gperf_generated) $(OBJ_FILES)
	$(CC) $(CFLAGS) -o $@ $?


$(OBJ_DIR):
	mkdir -p $(OBJ_DIRS)


bin: $(BIN)

clean:
	rm -rf $(OBJ_DIR) $(BIN) $(gperf_generated)

	