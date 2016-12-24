OCAMLBUILD=ocamlbuild -use-ocamlfind -use-menhir -no-links
# -use-ocamlfind: use the ocamlfind library manager
# -use-menhir: use the Menhir parser generator
# -no-links: do not create symlink from build outputs in _build into
#            the project directory

all: tests sourir

tests:
	$(OCAMLBUILD) tests.byte
	_build/tests.byte

sourir:
	$(OCAMLBUILD) sourir.byte
	cp _build/sourir.byte sourir

lib:
	$(OCAMLBUILD) sourir.cma

runtop: lib
	utop -require menhirLib -I _build parser_messages.cmo sourir.cma

run: sourir
	./sourir examples/sum.sou

test_examples: sourir
	for f in examples/*.sou; do yes 0 | ./sourir $$f > /dev/null; done

clean:
	ocamlbuild -clean

install-deps:
	opam pin add sourir . --no-action # tell opam about a local "sourir" package
	opam install --deps-only sourir # then install its dependencies

.PHONY: all run tests clean sourir test_examples

