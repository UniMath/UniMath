# -*- makefile-gmake -*-
UMAKEFILES += Makefile
ifneq "$(INCLUDE)" "no"
ifeq ($(shell test -f build/Makefile-configuration && echo yes),yes)
UMAKEFILES += build/Makefile-configuration
include build/Makefile-configuration
endif
endif
############################################
# The packages, listed in order by dependency:
PACKAGES += Foundations
PACKAGES += Combinatorics
PACKAGES += Algebra
PACKAGES += NumberSystems
PACKAGES += CategoryTheory
PACKAGES += Ktheory
PACKAGES += Topology
PACKAGES += RealNumbers
PACKAGES += Tactics
PACKAGES += SubstitutionSystems
PACKAGES += Folds
PACKAGES += HomologicalAlgebra
############################################
# other user options; see also build/Makefile-configuration-template
BUILD_COQ ?= yes
BUILD_COQIDE ?= no
COQBIN ?=
############################################
.PHONY: all everything install lc lcp wc describe clean distclean build-coq doc build-coqide
COQIDE_OPTION ?= no
ifeq "$(BUILD_COQ)" "yes"
COQBIN=sub/coq/bin/
all: check-first
all: build-coq
build-coq: sub/coq/bin/coqc
ifeq "$(BUILD_COQIDE)" "yes"
all: build-coqide
build-coqide: sub/coq/bin/coqide
COQIDE_OPTION := opt
endif
endif

# override the definition in build/CoqMakefile.make, to eliminate the -utf8 option
COQDOC := coqdoc
COQDOCFLAGS := -interpolate --charset utf-8
COQDOC_OPTIONS := -toc $(COQDOCFLAGS) $(COQDOCLIBS) -utf8

PACKAGE_FILES := $(patsubst %, UniMath/%/.package/files, $(PACKAGES))

ifneq "$(INCLUDE)" "no"
include build/CoqMakefile.make
endif
everything: TAGS all html install
check-first: enforce-prescribed-ordering check-travis
OTHERFLAGS += $(MOREFLAGS)
OTHERFLAGS += -indices-matter -w none
ifeq ($(VERBOSE),yes)
OTHERFLAGS += -verbose
endif

TYPE_IN_TYPE_FILES := 				\
	UniMath/Foundations/Resizing2.vo

$(TYPE_IN_TYPE_FILES) : OTHERFLAGS += -type-in-type

ENHANCEDDOCTARGET = enhanced-html
ENHANCEDDOCSOURCE = util/enhanced-doc
LATEXDIR = latex
COQDOCLATEXOPTIONS := -latex -utf8 --body-only

DEFINERS := 
DEFINERS := $(DEFINERS)Axiom\|
DEFINERS := $(DEFINERS)Class\|
DEFINERS := $(DEFINERS)CoFixpoint\|
DEFINERS := $(DEFINERS)CoInductive\|
DEFINERS := $(DEFINERS)Corollary\|
DEFINERS := $(DEFINERS)Definition\|
DEFINERS := $(DEFINERS)Example\|
DEFINERS := $(DEFINERS)Fact\|
DEFINERS := $(DEFINERS)Fixpoint\|
DEFINERS := $(DEFINERS)Function\|
DEFINERS := $(DEFINERS)Identity[[:space:]]+Coercion\|
DEFINERS := $(DEFINERS)Inductive\|
DEFINERS := $(DEFINERS)Instance\|
DEFINERS := $(DEFINERS)Lemma\|
DEFINERS := $(DEFINERS)Ltac\|
DEFINERS := $(DEFINERS)Module[[:space:]]+Import\|
DEFINERS := $(DEFINERS)Module\|
DEFINERS := $(DEFINERS)Notation\|
DEFINERS := $(DEFINERS)Proposition\|
DEFINERS := $(DEFINERS)Record\|
DEFINERS := $(DEFINERS)Remark\|
DEFINERS := $(DEFINERS)Scheme[[:space:]]+Equality[[:space:]]+for\|
DEFINERS := $(DEFINERS)Scheme[[:space:]]+Induction[[:space:]]+for\|
DEFINERS := $(DEFINERS)Scheme\|
DEFINERS := $(DEFINERS)Structure\|
DEFINERS := $(DEFINERS)Theorem

MODIFIERS := 
MODIFIERS := $(MODIFIERS)Canonical\|
MODIFIERS := $(MODIFIERS)Global\|
MODIFIERS := $(MODIFIERS)Local\|
MODIFIERS := $(MODIFIERS)Private\|
MODIFIERS := $(MODIFIERS)Program\|

COQDEFS := --language=none																\
	-r '/^[[:space:]]*\(\($(MODIFIERS)\)[[:space:]]+\)?\($(DEFINERS)\)[[:space:]]+\([[:alnum:]'\''_]+\)/\4/'					\
	-r "/^[[:space:]]*Notation.* \"'\([[:alnum:]'\''_]+\)'/\1/"											\
	-r '/^[[:space:]]*Tactic[[:space:]]+Notation.*[[:space:]]"\([[:alnum:]'\''_]+\)"[[:space:]]/\1/'										\
	-r '/^[[:space:]]*Delimit[[:space:]]+Scope[[:space:]]+[[:alnum:]'\''_]+[[:space:]]+with[[:space:]]+\([[:alnum:]'\''_]+\)[[:space:]]*\./\1/'

$(foreach P,$(PACKAGES),$(eval TAGS-$P: Makefile $(filter UniMath/$P/%,$(VFILES)); etags $(COQDEFS) -o $$@ $$^))
$(VFILES:.v=.vo) : $(COQBIN)coqc
TAGS : Makefile $(PACKAGE_FILES) $(VFILES); etags $(COQDEFS) $(VFILES)
FILES_FILTER := grep -vE '^[[:space:]]*(\#.*)?$$'
$(foreach P,$(PACKAGES),$(eval $P: check-first $(shell <UniMath/$P/.package/files $(FILES_FILTER) |sed "s=^\(.*\)=UniMath/$P/\1o=" )))
install:all
coqwc:; coqwc $(VFILES)
lc:; wc -l $(VFILES)
lcp:; for i in $(PACKAGES) ; do echo ; echo ==== $$i ==== ; for f in $(VFILES) ; do echo "$$f" ; done | grep "UniMath/$$i" | xargs wc -l ; done
wc:; wc -w $(VFILES)
admitted: 
	grep --color=auto Admitted $(VFILES)
axiom:
	grep --color=auto "Axiom " $(VFILES)
describe:; git describe --dirty --long --always --abbrev=40 --all
.coq_makefile_input: $(PACKAGE_FILES) $(UMAKEFILES)
	@ echo making $@ ; ( \
	echo '# -*- makefile-gmake -*-' ;\
	echo ;\
	echo '# DO NOT EDIT THIS FILE!' ;\
	echo '# It is made by automatically (by code in Makefile)' ;\
	echo ;\
	echo '-Q UniMath UniMath' ;\
	echo ;\
	for i in $(PACKAGES) ;\
	do <UniMath/$$i/.package/files $(FILES_FILTER) |sed "s=^=UniMath/$$i/="  ;\
	done ;\
	echo ;\
	echo '# Local ''Variables:' ;\
	echo '# compile-command: "sub/coq/bin/coq_makefile -f .coq_makefile_input -o CoqMakefile.make.tmp && mv CoqMakefile.make.tmp build/CoqMakefile.make"' ;\
	echo '# End:' ;\
	) >$@
# the '' above prevents emacs from mistaking the lines above as providing local variables when visiting this file
build/CoqMakefile.make: .coq_makefile_input $(COQBIN)coq_makefile
	$(COQBIN)coq_makefile -f .coq_makefile_input -o .coq_makefile_output
	mv .coq_makefile_output $@

# "clean::" occurs also in build/CoqMakefile.make, hence both colons
clean::
	rm -f .coq_makefile_input .coq_makefile_output build/CoqMakefile.make COQC.log
	find UniMath \( -name .\*.aux -o -name \*.glob -o -name \*.v.d -o -name \*.vo \) -delete
	find UniMath -type d -empty -delete
clean::; rm -rf $(ENHANCEDDOCTARGET)
latex-clean clean::; cd $(LATEXDIR) ; rm -f *.pdf *.tex *.log *.aux *.out *.blg *.bbl

distclean:: clean
distclean::          ; - $(MAKE) -C sub/coq distclean
distclean::          ; rm -f build/Makefile-configuration
distclean::          ; - $(MAKE) -C sub/lablgtk arch-clean

# building coq:
export PATH:=$(shell pwd)/sub/coq/bin:$(PATH)
sub/coq/configure.ml:
	git submodule update --init sub/coq
sub/coq/config/coq_config.ml: sub/coq/configure.ml
	: making $@ because of $?
	cd sub/coq && ./configure -coqide "$(COQIDE_OPTION)" -with-doc no -annotate -debug -local
# instead of "coqlight" below, we could use simply "theories/Init/Prelude.vo"
sub/coq/bin/coq_makefile sub/coq/bin/coqc: sub/coq/config/coq_config.ml
.PHONY: rebuild-coq
rebuild-coq sub/coq/bin/coq_makefile sub/coq/bin/coqc:
	$(MAKE) -w -C sub/coq KEEP_ML4_PREPROCESSED=true VERBOSE=true READABLE_ML4=yes coqbinaries tools states
sub/coq/bin/coqide: sub/coq/config/coq_config.ml
	$(MAKE) -w -C sub/coq KEEP_ML4_PREPROCESSED=true VERBOSE=true READABLE_ML4=yes coqide-binaries bin/coqide
configure-coq: sub/coq/config/coq_config.ml
git-describe:
	git describe --dirty --long --always --abbrev=40
	git submodule foreach git describe --dirty --long --always --abbrev=40 --tags
doc: $(GLOBFILES) $(VFILES) 
	mkdir -p $(ENHANCEDDOCTARGET)
	cp $(ENHANCEDDOCSOURCE)/proofs-toggle.js $(ENHANCEDDOCTARGET)/proofs-toggle.js
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d $(ENHANCEDDOCTARGET) \
	--with-header $(ENHANCEDDOCSOURCE)/header.html $(VFILES)
	sed -i'.bk' -f $(ENHANCEDDOCSOURCE)/proofs-toggle.sed $(ENHANCEDDOCTARGET)/*html

# Jason Gross' coq-tools bug isolator:
# The isolated bug will appear in this file, in the UniMath directory:
ISOLATED_BUG_FILE := isolated_bug.v
# To use it, run something like this command in an interactive shell:
#     make isolate-bug BUGGY_FILE=Foundations/Basics/PartB.v
sub/coq-tools/find-bug.py:
	git submodule update --init sub/coq-tools
help-find-bug:
	sub/coq-tools/find-bug.py --help
isolate-bug: sub/coq-tools/find-bug.py
	cd UniMath && \
	rm -f $(ISOLATED_BUG_FILE) && \
	../sub/coq-tools/find-bug.py --coqbin ../sub/coq/bin -R . UniMath \
		--arg " -indices-matter" \
		--arg " -type-in-type" \
		$(BUGGY_FILE) $(ISOLATED_BUG_FILE)
	@ echo "==="
	@ echo "=== the isolated bug has been deposited in the file UniMath/$(ISOLATED_BUG_FILE)"
	@ echo "==="

world: all html doc latex-doc

latex-doc: $(LATEXDIR)/doc.pdf

$(LATEXDIR)/doc.pdf : $(LATEXDIR)/helper.tex $(LATEXDIR)/references.bib $(LATEXDIR)/latex-preamble.txt $(LATEXDIR)/helper.tex $(LATEXDIR)/latex-epilogue.txt
	cd $(LATEXDIR) && cat latex-preamble.txt helper.tex latex-epilogue.txt > doc.tex
	cd $(LATEXDIR) && latexmk -pdf doc

$(LATEXDIR)/coqdoc.sty $(LATEXDIR)/helper.tex : $(VFILES:.v=.glob) $(VFILES)
	$(COQDOC) -Q UniMath UniMath $(COQDOC_OPTIONS) $(COQDOCLATEXOPTIONS) $(VFILES) -o $@

.PHONY: enforce-max-line-length
enforce-max-line-length:
	LC_ALL="en_US.UTF-8" gwc -L $(VFILES) | grep -vw total | awk '{ if ($$1 > 100) { printf "%6d  %s\n", $$1, $$2 }}' | sort -r | grep .
show-long-lines:
	LC_ALL="en_US.UTF-8" grep -nE '.{101}' $(VFILES)

# here we assume the shell is bash, which it usually is nowadays:
SHELL = bash
enforce-prescribed-ordering: .enforce-prescribed-ordering.okay
clean::; rm -f .enforce-prescribed-ordering.okay
.enforce-prescribed-ordering.okay: Makefile $(VFILES:.v=.v.d)
	: "--- enforce ordering prescribed by the files UniMath/*/.packages/files ---"
	@set -e ;\
	if declare -A seqnum 2>/dev/null ;\
	then n=0 ;\
	     for i in $(VOFILES) ;\
	     do n=$$(( $$n + 1 )) ;\
		seqnum[$$i]=$$n ;\
	     done ;\
	     for i in $(VFILES:.v=.v.d); \
	     do head -1 $$i ;\
	     done \
	     | sed -E -e 's/[^ ]*\.(glob|v\.beautified|v)([ :]|$$)/\2/g' -e 's/ *: */ /' \
	     | while read line ;\
	       do for i in $$line ; do echo $$i ; done \
		  | ( read target ; \
		      [ "$${seqnum[$$target]}" ] || (echo unknown target: $$target; false) >&2 ;\
		      while read prereq ; \
		      do [ "$${seqnum[$$prereq]}" ] || (echo "unknown prereq of $$target : $$prereq" ; false) >&2 ;\
			 echo "$$(($${seqnum[$$target]} > $${seqnum[$$prereq]})) error: *** $$target should not require $$prereq" ;\
		      done ) ;\
	       done | grep ^0 | sed 's/^0 //' | \
	       ( haderror= ; \
		 while read line ; \
		 do if [ ! "$$haderror" ] ; then haderror=1 ; fi ; \
		    echo "$$line" ;\
		 done ;\
		 [ ! "$$haderror" ] ) ;\
	else echo "make: *** skipping enforcement of linear ordering of packages, because 'bash' is too old" ;\
	fi
	touch $@

# here we ensure that the travis script checks every package
check-travis:.check-travis.okay
clean::; rm -f .check-travis.okay
.check-travis.okay: Makefile .travis.yml
	: --- check travis script ---
	@set -e ;\
	for p in $(PACKAGES) ;\
	do grep -q "PACKAGES=.*$$p" .travis.yml || ( echo "package $$p not checked by .travis.yml" >&2 ; exit 1 ) ;\
	done
	touch "$@"

#################################
# targets best used with INCLUDE=no
git-clean:
	git clean -Xdfq
	git submodule foreach git clean -xdfq
git-deinit:
	git submodule foreach git clean -xdfq
	git submodule deinit -f sub/*
#################################
