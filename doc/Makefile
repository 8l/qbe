.PHONY: all clean

all: html/abi.html html/il.html

clean:
	rm -fr html

html/%.html: %.txt
	mkdir html 2> /dev/null || true
	( echo "<!doctype html>"; \
	  echo "<link rel="stylesheet" href="http://c9x.me/css/simple.css" type="text/css" />"; \
	  echo '<div class="container">'; \
	  sed -ne '2{s,.*,<h2>&</h2>,;p;q}' $<; \
	  sed -e '1,3d' $< | ocaml txt.ml; \
	  echo '</div>'; \
	) > $@
