.PHONY: all test clean

all: bak

bak: elf.ml lo2.ml
	ocamlc -g -o bak elf.ml lo2.ml

test: bak
	@./bak test
	@cc -O2 -o t.out tmain.c t.o && ./t.out

clean:
	rm -f bak t *.o *.cm[io]
