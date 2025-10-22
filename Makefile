.DEFAULT_GOAL := build

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

.PHONY: build clean watch doc
