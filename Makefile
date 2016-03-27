.PHONY: all clean check
all clean:
	@make -C src $@
	@make -C minic $@
check: all
	test/go.sh all
