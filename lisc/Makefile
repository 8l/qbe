BIN = lisc
OBJ = parse.o ssa.o live.o isel.o main.o spill.o # rega.o emit.o main.o

CFLAGS = -Wall -Wextra -std=c99 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ)
