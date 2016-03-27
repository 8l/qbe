all clean:
	@make -C src $@
	@make -C minic $@
check: all
	test/go.sh all
sync-papers:
	unison -auto papers ssh://qcar@h/data/d/ssa-doc

.PHONY: all clean check sync-papers
