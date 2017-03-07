DOCS = abi il llvm

all: $(DOCS:%=html/%.html)

clean:
	rm -fr html

html/%.html: %.txt
	mkdir html 2> /dev/null || true
	( sed -ne '2{s,.*,<title>&</title>,;p;q}' $<; \
	  echo '<div class="container">'; \
	  sed -ne '2{s,.*,<h2>&</h2>,;p;q}' $<; \
	  sed -e '1,3d' $< | ocaml txt/txt.ml; \
	  echo '</div>'; \
	) > $@

.PHONY: all clean
