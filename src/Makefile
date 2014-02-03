# -*- makefile-gmake -*-
include Make-include.mk
OTHERFLAGS += -no-native-compiler
# OTHERFLAGS += -no-sharing
# OTHERFLAGS += -verbose
OTHERFLAGS += -indices-matter
# OTHERFLAGS += -init-file coqrc

TIME=gnu
ifeq ($(TIME),gnu)
TIMECMD = \time -f "%U sec, %M bytes: $*"
else
ifeq ($(TIME),bsd)
TIMECMD = \time -p
else
ifeq ($(TIME),bash)
TIMECMD = time -p
else
TIMECMD = time
endif
endif
endif

COQTIME = yes
ifeq ("$(COQTIME)","yes")
COQC = : compiling $*.v ; >$*.timing $(TIMECMD) $(COQBIN)coqc
OTHERFLAGS += -time
else
COQC = : compiling $*.v ; $(TIMECMD) $(COQBIN)coqc
endif

.PHONY: topten all everything install lc wc clean clean2 distclean
all:topten
topten: $(VOFILES)
	@find . -name \*.timing | while read x ;							\
	 do if [ -f "$$x" ] ;										\
	    then grep '^Chars' "$$x" | 									\
		 sed -e "s=^=$$x =" -e "s/timing/v/" -e "s/ Chars /:/" -e "s/ - \([0-9]*\)/-\1:/";	\
	    fi ;											\
	 done | sort -grk 3 | head -10

COQDOC := $(COQDOC) -utf8
COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Notation\|Proposition\|Module[[:space:]]+Import\|Module\)[[:space:]]+\([[:alnum:]'\''_]+\)/\2/'
TAGS : $(VFILES); etags $(COQDEFS) $^
install:all
everything: all TAGS html install
lc:; wc -l $(VFILES)
wc:; wc -w $(VFILES)
clean:clean2
clean2:; rm -f TAGS *.d *.glob N*.cmi N*.cmx N*.cmxs N*.native N*.o
distclean: clean; rm -f Make-include.mk Make-include.mk.bak

# override this on your system with the correct settings on the command line:
FOUNDATIONS_DIR := ../../Foundations2
REZK_COMPLETION_DIR := ../../RezkCompletion
FOUNDATIONS_FILES = $(shell cd $(FOUNDATIONS_DIR) && make show-vfiles)
REZK_COMPLETION_FILES = $(shell cd $(REZK_COMPLETION_DIR) && make show-vfiles)
html-all:
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html		\
		-R $(FOUNDATIONS_DIR) Foundations				\
		-R $(REZK_COMPLETION_DIR) RezkCompletion			\
		$(VFILES) $(FOUNDATIONS_FILES) $(REZK_COMPLETION_FILES) 
