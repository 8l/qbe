BIN = lisc
OBJ = parse.o ssa.o

CFLAGS = -Wall -Wextra -std=c99 -g

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ)
