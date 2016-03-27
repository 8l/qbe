all clean check:
	@make -C src $@
	@make -C minic $@

sync-papers:
	unison -auto papers ssh://qcar@h/data/d/ssa-doc

.PHONY: all clean check sync-papers
