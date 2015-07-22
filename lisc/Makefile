BIN = lisc
OBJ = main.o parse.o ssa.o live.o isel.o spill.o

CFLAGS = -Wall -Wextra -std=c11 -g -pedantic

$(BIN): $(OBJ)
	mv $@ $@.old 2>/dev/null || exit 0
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): lisc.h

.PHONY: clean
clean:
	rm -f $(BIN) $(OBJ) *.old
