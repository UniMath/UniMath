# -*- makefile-gmake -*-
M=.
P=Proof_of_Extensionality
COQ = time coqc
COQFLAGS = -opt -q
# in this list, put the prerequisites earlier, so TAGS is in the right order
VFILES :=					\
	$M/Generalities/uuu.v			\
	$M/Generalities/uu0.v			\
	$P/funextfun.v				\
	$M/hlevel1/hProp.v			\
	$M/hlevel2/hSet.v			\
	$M/hlevel2/algebra1a.v			\
	$M/hlevel2/algebra1b.v			\
	$M/hlevel2/algebra1c.v			\
	$M/hlevel2/algebra1d.v			\
	$M/hlevel2/hnat.v			\
	$M/hlevel2/stnfsets.v			\
	$M/hlevel2/finitesets.v			\
	$M/hlevel2/hz.v				\
	$M/hlevel2/hq.v
VOFILES := $(VFILES:.v=.vo)
DOCFILES := doc/index.html
%.glob %.vo: %.v
	@ echo "make: Entering directory \`$(dir $*)'"
	cd $(dir $*) && $(COQ) $(COQFLAGS) $(notdir $*.v)
	@ echo "make: Leaving directory \`$(dir $*)'"
all: TAGS $(VOFILES) $(DOCFILES)
COQDEFS := -r "/^[[:space:]]*\(Inductive\|Record\|Definition\|Corollary\|Axiom\|Theorem\|Notation\|Fixpoint\|Let\|Hypothesis\|Lemma\)[[:space:]]+['[:alnum:]_]+/"
TAGS : $(VFILES); etags --language=none $(COQDEFS) $^
Makefile.depends:; find . -name \*.v | >$@ xargs coqdep -I $M/Generalities -I $M/hlevel1 -I $M/hlevel2 -I $P
include Makefile.depends
MADE_FILES += doc
$(DOCFILES): $(VFILES); mkdir -p doc && cd doc && ( find ../$M ../$P -name \*.v | xargs coqdoc -toc )
clean:
	rm -rf $(MADE_FILES)
	find $M $P \( \
		-name \*.aux -o \
		-name \*.dvi -o \
		-name \*.idx -o \
		-name \*.log -o \
		-name \*.glob -o \
		-name \*.vo -o \
		-name \*.pdf \
		\) -print -delete
