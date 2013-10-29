# -*- makefile-gmake -*-
# e.g., put TIMER=time on the command line
COQ = $(TIMER) coqc
COQFLAGS = -opt -q -I ../Generalities -I ../hlevel1
# in this list, put the prerequisites earlier, so TAGS is in the right order
VFILES :=					\
	Generalities/uuu.v			\
	Generalities/uu0.v			\
	Proof_of_Extensionality/funextfun.v	\
	hlevel1/hProp.v				\
	hlevel2/hSet.v				\
	hlevel2/algebra1a.v			\
	hlevel2/algebra1b.v			\
	hlevel2/algebra1c.v			\
	hlevel2/algebra1d.v			\
	hlevel2/hnat.v				\
	hlevel2/stnfsets.v			\
	hlevel2/finitesets.v			\
	hlevel2/hz.v				\
	hlevel2/hq.v
VOFILES := $(VFILES:.v=.vo)
DOCFILES := doc/index.html
%.glob %.vo: %.v
	@ echo "make: Entering directory \`$(dir $*)'"
	cd $(dir $*) && $(COQ) $(COQFLAGS) $(notdir $*.v)
	@ echo "make: Leaving directory \`$(dir $*)'"
all: TAGS $(VOFILES) $(DOCFILES)
COQDEFS := -r "/^[[:space:]]*\(Inductive\|Record\|Definition\|Corollary\|Axiom\|Theorem\|Notation\|Fixpoint\|Let\|Hypothesis\|Lemma\)[[:space:]]+['[:alnum:]_]+/"
TAGS : $(VFILES); etags --language=none $(COQDEFS) $^
Makefile.depends:; find . -name \*.v | >$@ xargs coqdep -I Generalities -I hlevel1 -I hlevel2 -I Proof_of_Extensionality
include Makefile.depends
$(DOCFILES): $(VFILES); mkdir -p doc && cd doc && ( find .. -name \*.v | xargs coqdoc -toc )
# don't bother removing Makefile.depends, because then make will complain about it
clean:
	rm -rf doc TAGS
	find . \(				\
		-name \*.aux -o			\
		-name \*.dvi -o			\
		-name \*.idx -o			\
		-name \*.log -o			\
		-name \*.glob -o		\
		-name \*.vo -o			\
		-name \*.pdf			\
		\) -print -delete
