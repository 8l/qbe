.PHONY: all clean

DOCS = abi il

all: $(DOCS:%=html/%.html) html/txt.css

html/txt.css: txt/txt.css
	cp -f $< $@

clean:
	rm -fr html

html/%.html: %.txt
	mkdir html 2> /dev/null || true
	( echo '<!doctype html>'; \
	  echo '<link rel="stylesheet"' \
	  	'href="http://c9x.me/css/simple.css"' \
	  	'type="text/css" />'; \
	  echo '<link rel="stylesheet"' \
	  	'href="txt.css"' \
	  	'type="text/css" />'; \
	  sed -ne '2{s,.*,<title>&</title>,;p;q}' $<; \
	  echo '<div class="container">'; \
	  sed -ne '2{s,.*,<h2>&</h2>,;p;q}' $<; \
	  sed -e '1,3d' $< | ocaml txt/txt.ml; \
	  echo '</div>'; \
	) > $@
