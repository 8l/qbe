BIN = lisc
# OBJ = main.o util.o parse.o mem.o ssa.o copy.o live.o isel.o spill.o rega.o emit.o
OBJ = main.o util.o parse.o ssa.o

CFLAGS = -Wall -Wextra -std=c99 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean syndoc
clean:
	rm -f $(BIN) $(OBJ)
syndoc:
	unison -auto doc ssh://qcar@h/data/d/ssa-doc
