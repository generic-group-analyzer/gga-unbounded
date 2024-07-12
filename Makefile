OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind -quiet -ocamlc ocamlc -ocamlopt ocamlopt
COREFLAGS=-pkg core_kernel \
    -pkg ppx_compare,ppx_sexp_conv,ppx_hash \
    -pkg ppx_bin_prot \
    -tag short_paths \
    -cflags -strict-sequence

DESTDIR    =
PREFIX     ?= /usr/local
INSTALL    := scripts/install/install-sh

BINDIR := $(DESTDIR)$(PREFIX)/bin
LIBDIR := $(DESTDIR)$(PREFIX)/lib/generic-unbounded
SHRDIR := $(DESTDIR)$(PREFIX)/share/generic-unbounded

.PHONY: install wsubt.native ubt.native

all: ubt.native wsubt.native

ubt.native:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./ubt.native

wsubt.native:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./wsubt.native

install: ubt.native wsubt.native
	$(INSTALL) -m 0755 -d $(BINDIR)
	$(INSTALL) -m 0755 -T ubt.native $(BINDIR)/generic-group-unbounded
	$(INSTALL) -m 0755 -T wsubt.native $(BINDIR)/generic-group-unbounded-ws

# OCAMLDEP= ocamlfind ocamldep -package core_kernel \
#             -package ppx_jane \
#             -I src one-line

dev:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) Wparser.cmx


%.deps :
	$(OCAMLDEP) src/$(basename $@).ml> .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg

depgraph :
	$(OCAMLDEP) src/*.ml src/*.mli \
        | grep -v Test | grep -v Extract > .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg
