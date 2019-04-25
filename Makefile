BIN = qbe

V = @
OBJDIR = obj

SRC      = main.c util.c parse.c cfg.c mem.c ssa.c alias.c load.c copy.c \
           fold.c live.c spill.c rega.c gas.c
AMD64SRC = amd64/targ.c amd64/sysv.c amd64/isel.c amd64/emit.c
ARM64SRC = arm64/targ.c arm64/abi.c arm64/isel.c arm64/emit.c
SRCALL   = $(SRC) $(AMD64SRC) $(ARM64SRC)

AMD64OBJ = $(AMD64SRC:%.c=$(OBJDIR)/%.o)
ARM64OBJ = $(ARM64SRC:%.c=$(OBJDIR)/%.o)
OBJ      = $(SRC:%.c=$(OBJDIR)/%.o) $(AMD64OBJ) $(ARM64OBJ)

CFLAGS += -Wall -Wextra -std=c99 -g -pedantic

$(OBJDIR)/$(BIN): $(OBJ) $(OBJDIR)/timestamp
	@test -z "$(V)" || echo "ld $@"
	$(V)$(CC) $(LDFLAGS) $(OBJ) -o $@

$(OBJDIR)/%.o: %.c $(OBJDIR)/timestamp
	@test -z "$(V)" || echo "cc $<"
	$(V)$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/timestamp:
	@mkdir -p $(OBJDIR)
	@mkdir -p $(OBJDIR)/amd64
	@mkdir -p $(OBJDIR)/arm64
	@touch $@

$(OBJ): all.h ops.h
$(AMD64OBJ): amd64/all.h
$(ARM64OBJ): arm64/all.h
$(OBJDIR)/main.o: config.h

config.h:
	@case `uname` in                               \
	*Darwin*)                                      \
		echo "#define Defasm Gasmacho";        \
		echo "#define Deftgt T_amd64_sysv";    \
		;;                                     \
	*)                                             \
		echo "#define Defasm Gaself";          \
		case `uname -m` in                     \
		*aarch64*)                             \
			echo "#define Deftgt T_arm64"; \
			;;                             \
		*)                                     \
			echo "#define Deftgt T_amd64_sysv";\
			;;                             \
		esac                                   \
		;;                                     \
	esac > $@

install: $(OBJDIR)/$(BIN)
	mkdir -p "$(DESTDIR)/$(PREFIX)/bin/"
	cp $< "$(DESTDIR)/$(PREFIX)/bin/"

uninstall:
	rm -f "$(DESTDIR)/$(PREFIX)/bin/$(BIN)"

clean:
	rm -fr $(OBJDIR)

clean-gen: clean
	rm -f config.h

check: $(OBJDIR)/$(BIN)
	tools/test.sh all

check-arm64: $(OBJDIR)/$(BIN)
	TARGET=arm64 tools/test.sh all

src:
	@echo $(SRCALL)

80:
	@for F in $(SRCALL);                       \
	do                                         \
		awk "{                             \
			gsub(/\\t/, \"        \"); \
			if (length(\$$0) > $@)     \
				printf(\"$$F:%d: %s\\n\", NR, \$$0); \
		}" < $$F;                          \
	done

.PHONY: clean clean-gen check check-arm64 src 80 install uninstall
