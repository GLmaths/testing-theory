.DEFAULT_GOAL := build
DOC_DIR := doc
BUILD_DIR := _build/default/theories
EXTRA_DIR := doc-config
COQDOC_FLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  -d $(DOC_DIR) \
	--no-lib-name \
  --index indexpage \
	-s \
	--with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html

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
	rocq doc $(COQDOC_FLAGS) -R $(BUILD_DIR) TestingTheory `find $(BUILD_DIR) -name *.v | sort`
	chmod +w $(DOC_DIR)
	cp $(EXTRA_DIR)/* $(DOC_DIR)

.PHONY: build clean watch doc
