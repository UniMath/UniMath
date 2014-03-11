# -*- makefile-gmake -*-
include Makefile-coq.make
everything: TAGS all html install
OTHERFLAGS += -indices-matter
Packages/Foundations/hlevel2/algebra1b.vo : OTHERFLAGS += -no-sharing
ifeq ($(VERBOSE),yes)
OTHERFLAGS += -verbose
endif

# later: see exactly which files need -no-sharing
NO_SHARING = yes
ifeq ($(NO_SHARING),yes)
OTHERFLAGS += -no-sharing
endif
# TIME = time
COQDOC := $(COQDOC) -utf8
COQC = $(TIME) $(COQBIN)coqc
COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Notation\|Proposition\|Module[[:space:]]+Import\|Module\)[[:space:]]+\([[:alnum:]'\''_]+\)/\2/'
TAGS : $(VFILES); etags $(COQDEFS) $^
install:all
lc:; wc -l $(VFILES)
wc:; wc -w $(VFILES)
clean:clean2
clean2:
describe:; git describe --dirty --long --always --abbrev=40 --all

