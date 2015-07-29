BIN = lisc
OBJ = main.o parse.o ssa.o live.o isel.o spill.o rega.o emit.o

CFLAGS = -Wall -Wextra -std=c11 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ)
