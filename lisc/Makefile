BIN = lisc
OBJ = parse.o ssa.o

CFLAGS = -Wall -Wextra -std=c99 -g

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ)
