OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind -quiet -ocamlc ocamlc -ocamlopt ocamlopt
COREFLAGS=-pkg core_kernel \
    -pkg sexplib.syntax,comparelib.syntax,fieldslib.syntax,variantslib.syntax \
    -pkg bin_prot.syntax \
    -tag short_paths \
    -cflags -strict-sequence

DESTDIR    =
PREFIX     ?= /usr/local
INSTALL    := scripts/install/install-sh

BINDIR := $(DESTDIR)$(PREFIX)/bin
LIBDIR := $(DESTDIR)$(PREFIX)/lib/generic-unbounded
SHRDIR := $(DESTDIR)$(PREFIX)/share/generic-unbounded

.PHONY: install wsubt.native ubt.native notabs

all: wsubt.native ubt.native

ubt.native: notabs
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./ubt.native

wsubt.native: notabs
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./wsubt.native

install: ubt.native wsubt.native
	$(INSTALL) -m 0755 -d $(BINDIR)
	$(INSTALL) -m 0755 -T ubt.native $(BINDIR)/generic-group-unbounded
	$(INSTALL) -m 0755 -T wsubt.native $(BINDIR)/generic-group-unbounded-ws

OCAMLDEP= ocamlfind ocamldep -package core_kernel -syntax camlp4o \
            -package comparelib.syntax -package sexplib.syntax -package fieldslib.syntax \
            -I src one-line

notabs:
	! grep -P '\t' src/*.ml src/*.mli

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
