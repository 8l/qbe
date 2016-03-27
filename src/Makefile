BIN = qbe
OBJ = main.o util.o parse.o mem.o ssa.o copy.o live.o isel.o spill.o rega.o emit.o

CFLAGS += -Wall -Wextra -std=c99 -g -pedantic

$(BIN): $(OBJ)
	$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJ): all.h config.h

config.h:
	@case `uname` in                                \
	*Darwin*) echo "#define Defaultasm Gasmacho" ;; \
	*Linux*)  echo "#define Defaultasm Gaself" ;;   \
	esac > $@


all: $(BIN)
clean:
	rm -f $(BIN) $(OBJ)
check:
	make -C .. check

.PHONY: all clean check syndoc
