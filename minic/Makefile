CFLAGS=-g -Wall

minic: yacc minic.y
	./yacc minic.y
	$(CC) $(CFLAGS) -o $@ y.tab.c
clean:
	rm -f yacc minic y.*
.PHONY: clean
