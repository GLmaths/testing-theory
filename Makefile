.DEFAULT_GOAL := build
DOC_DIR := doc
BUILD_DIR := _build/default/theories

build:
	dune build @all

clean:
	dune clean

# Watch mode — rebuild automatically when files change
watch:
	dune build @all --watch

# Generate HTML documentation
# bypass dune 3.17, not mature enough
doc:
	# make sure dune build the files
	dune build
	mkdir -p $(DOC_DIR)
	rm -Rf $(DOC_DIR)/*
	coqdoc --toc --html -R $(BUILD_DIR) Must --with-header doc-config/header.html --with-footer doc-config/footer.html $(BUILD_DIR)/*.v -d $(DOC_DIR)
	chmod +w $(DOC_DIR)
	mv $(DOC_DIR)/index.html $(DOC_DIR)/indexpage.html 
	cp doc-config/* $(DOC_DIR)

.PHONY: build clean watch doc
