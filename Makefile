.PHONY: all test clean

all: bak

bak: elf.ml lo2.ml
	ocamlc -g -o bak elf.ml lo2.ml

test: bak
	@./bak test
	@cc -o t tmain.c t.o && ./t

clean:
	rm -f bak t t.o
