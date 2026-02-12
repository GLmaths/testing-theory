.DEFAULT_GOAL := build
DOCDIR := doc

build:
	dune build @all

clean:
	dune clean

# Watch mode — rebuild automatically when files change
watch:
	dune build @all --watch

# Generate HTML documentation (if dune files define doc targets)
doc:
	dune build @doc
	mkdir -p $(DOCDIR)
	rm -Rf $(DOCDIR)/*
	cp -r _build/default/theories/Must.html/* $(DOCDIR)
	chmod +w $(DOCDIR)/* # allow overriding previously generated files
	mv $(DOCDIR)/index.html $(DOCDIR)/indexpage.html 
	cp doc-config/* $(DOCDIR)

.PHONY: build clean watch doc
