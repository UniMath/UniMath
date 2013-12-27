# -*- makefile-gmake -*-
include Make-include.mk
TIMECMD = time -p
# OTHERFLAGS = -verbose
COQDOC := $(COQDOC) -utf8
COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Notation\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]'\''_]+\)/\2/'
TAGS : $(VFILES); etags $(COQDEFS) $^
install:all
lc:; wc -l $(VFILES)
clean:clean2
clean2:; rm -f TAGS *.d *.glob N*.cmi N*.cmx N*.cmxs N*.native N*.o
