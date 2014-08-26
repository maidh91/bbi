CAMLC	 	= ocamlfind ocamlc
CAMLOPT		= ocamlfind ocamlopt
CAMLCFLAG 	= -annot -package core,sexplib.syntax -syntax camlp4o -thread

CAMLBUILD	= ocamlbuild
CAMLBUILDFLAG	= -use-ocamlfind -cflags "-g -annot" -no-hygiene -I checker -I converter -I interactive

all : 
	$(CAMLBUILD) $(CAMLBUILDFLAG) CUI.native

Prover.cmo : LBBI.cmi

Interactive.cmo : Interactive.cmi
Interactive.cmi : Prover.cmo

ProofChecker.cmo : ProofChecker.cmi
ProofChecker.cmi : Common.cmi

LBBI.cmo : LSeq.cmi
LBBI.cmi : LSeq.cmi

LSeq.cmo : LSeq.cmi
LSeq.cmi : Prop.cmi

Prop.cmo : Prop.cmi
Prop.cmi : Common.cmi

clean: lclean
	ocamlbuild -clean	

lclean:
	rm -f *.annot *.aux *.log *.cm[iox] *.div *BBI*.tex

.SUFFIXES : .ml .mli .cmo .cmi .cmx .c .o .native .byte
.ml.cmo: $<
	$(CAMLC) $(CAMLCFLAG) -c $< -o $@
.ml.cmx: $<
	$(CAMLOPT) $(CAMLCFLAG) -c $< -o $@
.mli.cmi: $<
	$(CAMLC) $(CAMLCFLAG) -c $< -o $@
.ml.native: $<
	$(CAMLBUILD) $(CAMLBUILDFLAG) $@
.ml.byte: $<
	$(CAMLBUILD) $(CAMLBUILDFLAG) $@
.c.o: $<
	$(CC) $(CFLAG) -c $< -o $@
