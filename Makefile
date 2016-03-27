.PHONY: all check
all:
	@make -C src
check: all
	test/go.sh all
