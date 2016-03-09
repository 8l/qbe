BIN = lisc
OBJ = main.o util.o parse.o mem.o ssa.o copy.o live.o isel.o spill.o rega.o emit.o

CFLAGS = -Wall -Wextra -std=c99 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean check syndoc
clean:
	rm -f $(BIN) $(OBJ)
check: $(BIN)
	test/go.sh all
syndoc:
	unison -auto doc ssh://qcar@h/data/d/ssa-doc
