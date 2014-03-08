# -*- makefile-gmake -*-
everything: TAGS all topten html-all
include Make-include.mk
# OTHERFLAGS += -no-native-compiler
# OTHERFLAGS += -no-sharing
# OTHERFLAGS += -verbose
OTHERFLAGS += -indices-matter
# OTHERFLAGS += -init-file coqrc

TIME=
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
lc:; wc -l $(VFILES)
wc:; wc -w $(VFILES)
clean:clean2
clean2::; rm -f TAGS *.d *.glob N*.cmi N*.cmx N*.cmxs N*.native N*.o coqdoc.sty
distclean: clean; rm -f Make-include.mk Make-include.mk.bak

# override this on your system with the correct settings on the command line:
COQ_DIR = ../../DanGrayson-coq
FOUNDATIONS_DIR := ../../Foundations2
REZK_COMPLETION_DIR := ../../RezkCompletion
FOUNDATIONS_FILES = $(shell cd $(FOUNDATIONS_DIR) && make show-vfiles)
REZK_COMPLETION_FILES = $(shell cd $(REZK_COMPLETION_DIR) && make show-vfiles)
ALL_FILES = $(VFILES) $(REZK_COMPLETION_FILES) $(FOUNDATIONS_FILES)
BASE = Ktheory-doc
doc: all html-all # $(BASE).pdf
html-all: $(ALL_FILES)
	rm -rf html-all
	mkdir html-all
	$(COQDOC) -toc $(COQDOCFLAGS) --html $(COQDOCLIBS) -d html-all	\
		-R $(FOUNDATIONS_DIR) Foundations				\
		-R $(REZK_COMPLETION_DIR) RezkCompletion			\
		$(ALL_FILES) 
clean2::; rm -rf html-all
coqdoc.sty $(BASE).tex: $(ALL_FILES)
	rm -f $(BASE).*
	$(COQDOC) -toc $(COQDOCFLAGS) --latex $(COQDOCLIBS) -d html-all	\
		-o $(BASE).tex							\
		-R $(FOUNDATIONS_DIR) Foundations				\
		-R $(REZK_COMPLETION_DIR) RezkCompletion			\
		$(ALL_FILES)
$(BASE).pdf : $(BASE).tex
	pdflatex $^
	pdflatex $^
clean2::; rm -rf $(BASE).*
describe:
	@ for i in $(COQ_DIR) $(FOUNDATIONS_DIR) $(REZK_COMPLETION_DIR) ; do \
	    ( cd $$i && echo ======= $$i ; set -x ; \
	    git remote -vv && \
	    git describe --dirty --long --always --abbrev=40 --all ) ;\
	done
publish:html-all;rsync -av html-all/. u00:public_html/Ktheory/.
