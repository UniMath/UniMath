# -*- makefile-gmake -*-
# e.g., put TIMER=time on the command line
all: TAGS
include Make.makefile
COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_]+\)/\2/'
TAGS : $(VFILES); etags $(COQDEFS) $^
clean:clean2
clean2:; rm -f TAGS
