.PHONY: all test

all: bak

bak: elf.ml lo2.ml
	ocamlc -o bak elf.ml lo2.ml

test: bak
	./bak test
	cc -o t tmain.c t.o
	./t
