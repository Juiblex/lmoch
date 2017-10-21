OCAMLBUILD= ocamlbuild -no-links -classic-display \
		-libs unix,nums \
		-pkg Z3 \
		-tags debug,annot

TARGET=native
MAIN=lmoch

all: $(MAIN)

native: TARGET := native
native: all
opt: native
$(MAIN).opt: native
$(MAIN).native: native


byte: TARGET := byte
byte: all
$(MAIN).byte: byte


$(MAIN): $(MAIN).target
	cp _build/$(MAIN).$(TARGET) $(MAIN)

$(MAIN).target:
	(cd _build; \
	/Users/theotime/.opam/4.03.0/bin/ocamlopt.opt unix.cmxa nums.cmxa -I /Users/theotime/.opam/4.03.0/lib/Z3 -I /Users/theotime/.opam/4.03.0/lib/num -I /Users/theotime/.opam/4.03.0/lib/ocaml /Users/theotime/.opam/4.03.0/lib/Z3/z3ml.cmxa -g asttypes.cmx ident.cmx typed_ast.cmx util.cmx flatten.cmx inline.cmx parse_ast.cmx parser.cmx lexer.cmx scheduling.cmx solve.cmx typed_ast_printer.cmx typing.cmx lmoch.cmx -o lmoch.native)

clean:
	ocamlbuild -classic-display -clean

realclean: clean
	rm -f $(MAIN) *~

cleanall: realclean
