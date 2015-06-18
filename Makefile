OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind -quiet -ocamlc ocamlc -ocamlopt ocamlopt
COREFLAGS=-pkg core \
    -pkg sexplib.syntax,comparelib.syntax,fieldslib.syntax,variantslib.syntax \
    -pkg bin_prot.syntax \
    -tag short_paths \
    -cflags -strict-sequence

.PHONY: ubt wsubt

all: wsubt # ubt

ubt:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./ubt.native
	./ubt.native

wsubt:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./wsubt.native
	killall wsubt.native

