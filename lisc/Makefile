BIN = lisc
OBJ = parse.o ssa.o live.o isel.o spill.o rega.o main.o # emit.o main.o

CFLAGS = -Wall -Wextra -std=c11 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ)
