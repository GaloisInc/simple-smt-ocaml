.PHONY: docs clean

docs:
	dune build @doc
	rm -rf docs && cp -r _build/default/_doc/_html docs

