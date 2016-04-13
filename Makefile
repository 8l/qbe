BIN = qbe
ABI = sysv

V = @
OBJDIR = obj

SRC = main.c util.c parse.c mem.c ssa.c copy.c fold.c live.c $(ABI).c isel.c spill.c rega.c emit.c
OBJ = $(SRC:%.c=$(OBJDIR)/%.o)

CFLAGS += -Wall -Wextra -std=c99 -g -pedantic

$(OBJDIR)/$(BIN): $(OBJ) $(OBJDIR)/timestamp
	@test -z "$(V)" || echo "ld $@"
	$(V)$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJDIR)/%.o: %.c $(OBJDIR)/timestamp
	@test -z "$(V)" || echo "cc $<"
	$(V)$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/timestamp:
	@mkdir -p $(OBJDIR)
	@touch $@

$(OBJ): all.h
obj/main.o: config.h

config.h:
	@case `uname` in                                 \
	*Darwin*)  echo "#define Defaultasm Gasmacho" ;; \
	*)         echo "#define Defaultasm Gaself" ;;   \
	esac > $@

clean:
	rm -fr $(OBJDIR)

clean-gen: clean
	rm -f config.h

check: $(OBJDIR)/$(BIN)
	tools/unit.sh all

80:
	@for F in $(SRC);                          \
	do                                         \
		awk "{                             \
			gsub(/\\t/, \"        \"); \
			if (length(\$$0) > $@)     \
				printf(\"$$F:%d: %s\\n\", NR, \$$0); \
		}" < $$F;                          \
	done

.PHONY: clean clean-gen check 80 syndoc
