.PHONY: all check
all:
	@make -C $@
check: all
	test/go.sh all
