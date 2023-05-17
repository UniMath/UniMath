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
PACKAGES += MoreFoundations
PACKAGES += Combinatorics
PACKAGES += Algebra
PACKAGES += Tactics
PACKAGES += NumberSystems
PACKAGES += SyntheticHomotopyTheory
PACKAGES += PAdics
PACKAGES += CategoryTheory
PACKAGES += Bicategories
PACKAGES += Ktheory
PACKAGES += Topology
PACKAGES += RealNumbers
PACKAGES += SubstitutionSystems
PACKAGES += Folds
PACKAGES += HomologicalAlgebra
PACKAGES += AlgebraicGeometry
PACKAGES += Paradoxes
PACKAGES += Induction
PACKAGES += AlgebraicTheories
PACKAGES += Semantics
############################################
# other user options; see also build/Makefile-configuration-template
BUILD_COQ ?= no
BUILD_COQIDE ?= no
DEBUG_COQ ?= no
COQBIN ?=
MEMORY_LIMIT ?= 2500000
LIMIT_MEMORY ?= no
############################################
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
############################################
export COQBIN
############################################

.PHONY: all everything install lc lcp wc describe clean distclean build-coq doc build-coqide html sanity-checks other-checks
.PHONY all: make-summary-files
everything: TAGS all html install
.PHONY sanity-checks:  check-prescribed-ordering	\
		check-listing-of-proof-files		\
		check-for-change-to-Foundations		\
		check-for-submodule-changes		\
		check-for-changes-to-CONTENTS.md
.PHONY other-checks:   check-max-line-length

# empty target prevents implicit rule search, saving time
Makefile :;

COQIDE_OPTION := no

ifeq "$(BUILD_COQ)" "yes"
COQBIN=sub/coq/bin/
all: build-coq
build-coq: sub/coq/bin/coqc
ifeq "$(BUILD_COQIDE)" "yes"
all: build-coqide
COQIDE_OPTION := opt
endif
endif

COQ_PATH := -Q UniMath UniMath

# override the definition in build/CoqMakefile.make, to eliminate the -utf8 option
COQDOC := coqdoc
COQDOCFLAGS := -interpolate --charset utf-8 $(COQ_PATH)
COQDOC_OPTIONS := -toc $(COQDOCFLAGS) $(COQDOCLIBS) -utf8

PACKAGE_FILES := $(patsubst %, UniMath/%/.package/files, $(PACKAGES))

ifneq "$(INCLUDE)" "no"
include .coq_makefile_output.conf
VFILES := $(COQMF_VFILES)
VOFILES := $(VFILES:.v=.vo)
endif

ifeq ($(BUILD_COQ),yes)
$(VOFILES) : $(COQBIN)coqc
endif

ifeq ($(LIMIT_MEMORY),yes)
EFFECTIVE_MEMORY_LIMIT = $(MEMORY_LIMIT)
else
EFFECTIVE_MEMORY_LIMIT = unlimited
endif

install: build/CoqMakefile.make
	ulimit -v $(EFFECTIVE_MEMORY_LIMIT) ; $(MAKE) -f build/CoqMakefile.make $@
all html uninstall: build/CoqMakefile.make
	ulimit -v $(EFFECTIVE_MEMORY_LIMIT) ; $(MAKE) -f build/CoqMakefile.make $@
clean:: build/CoqMakefile.make
	$(MAKE) -f build/CoqMakefile.make $@
distclean:: build/CoqMakefile.make
	$(MAKE) -f build/CoqMakefile.make cleanall archclean

WARNING_FLAGS := -notation-overridden
OTHERFLAGS += $(MOREFLAGS)
OTHERFLAGS += -noinit -indices-matter -type-in-type -w '\'"$(WARNING_FLAGS)"\''
ifeq ($(VERBOSE),yes)
OTHERFLAGS += -verbose
endif
ENHANCEDDOCTARGET = enhanced-html
ENHANCEDDOCSOURCE = util/enhanced-doc
LATEXDIR = latex
COQDOCLATEXOPTIONS := -latex -utf8 --body-only

DEFINERS := 
DEFINERS := $(DEFINERS)Axiom\|
DEFINERS := $(DEFINERS)Class\|
DEFINERS := $(DEFINERS)Coercion\|
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
DEFINERS := $(DEFINERS)Theorem\|
DEFINERS := $(DEFINERS)Universe

MODIFIERS := 
MODIFIERS := $(MODIFIERS)Canonical\|
MODIFIERS := $(MODIFIERS)Monomorphic\|
MODIFIERS := $(MODIFIERS)Global\|
MODIFIERS := $(MODIFIERS)Local\|
MODIFIERS := $(MODIFIERS)Private\|
MODIFIERS := $(MODIFIERS)Program\|

COQDEFS := --language=none											\
	-r '/^[ \t]*\(\($(MODIFIERS)\)[ \t]+\)?\($(DEFINERS)\)[ \t]+\([0-9A-Za-z'\''_]+\)/\4/'			\
	-r "/^[ \t]*Notation.* \"'\([0-9A-Za-z'\''_]+\)'/\1/"							\
	-r '/^[ \t]*Tactic[ \t]+Notation.*[ \t]"\([0-9A-Za-z'\''_]+\)"[ \t]/\1/'				\
	-r '/^[ \t]*Delimit[ \t]+Scope[ \t]+[0-9A-Za-z'\''_]+[ \t]+with[ \t]+\([0-9A-Za-z'\''_]+\)[ \t]*\./\1/'

# this function reverses the order of items in a list
reverse = $(if $(1),$(call reverse,$(wordlist 2,$(words $(1)),$(1)))) $(firstword $(1))

$(foreach P,$(PACKAGES),$(eval TAGS-$P: Makefile $(filter UniMath/$P/%,$(VFILES)); etags $(COQDEFS) -o $$@ $$^))
TAGS : Makefile $(PACKAGE_FILES) $(VFILES)
	$(SHOW)ETAGS
	$(HIDE)etags $(COQDEFS) $(VFILES)
FILES_FILTER := grep -vE '^[ \t]*(\#.*)?$$'
FILES_FILTER_2 := grep -vE '^[ \t]*(\#.*)?$$$$'
$(foreach P,$(PACKAGES),												\
	$(eval $P: make-summary-files build/CoqMakefile.make UniMath/.dir-locals.el;								\
		+ ulimit -v $(EFFECTIVE_MEMORY_LIMIT) ;									\
		  $(MAKE) -f build/CoqMakefile.make									\
			$(shell <UniMath/$P/.package/files $(FILES_FILTER) |sed "s=^\(.*\).v=UniMath/$P/\1.vo=" )	\
			UniMath/$P/All.vo))

$(foreach v,$(VFILES), $(eval $v.vo: $v.v; ulimit -v $(EFFECTIVE_MEMORY_LIMIT) ; $(MAKE) -f build/CoqMakefile.make $v.vo))

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
	@echo --- making $@ ; ( \
	echo '# -*- makefile-gmake -*-' ;\
	echo ;\
	echo '# DO NOT EDIT THIS FILE!' ;\
	echo '# It is made by automatically (by code in Makefile)' ;\
	echo ;\
	echo 'INSTALLDEFAULTROOT = UniMath';\
	echo ;\
	echo '$(COQ_PATH)' ;\
	echo '-arg "$(OTHERFLAGS)"' ;\
	echo ;\
	for i in $(PACKAGES) ;\
	do <UniMath/$$i/.package/files $(FILES_FILTER) |sed "s=^=UniMath/$$i/="  ;\
	   echo UniMath/$$i/All.v ;\
	done ;\
	echo UniMath/All.v ;\
	echo ;\
	echo '# Local ''Variables:' ;\
	echo '# compile-command: "$(COQBIN)coq_makefile -f .coq_makefile_input -o CoqMakefile.make.tmp && mv CoqMakefile.make.tmp build/CoqMakefile.make"' ;\
	echo '# End:' ;\
	) >$@
# the '' above prevents emacs from mistaking the lines above as providing local variables when visiting this file

ifdef COQBIN
build/CoqMakefile.make .coq_makefile_output.conf: $(COQBIN)coq_makefile
endif
build/CoqMakefile.make .coq_makefile_output.conf: .coq_makefile_input
	$(COQBIN)coq_makefile -f .coq_makefile_input -o .coq_makefile_output
	mv .coq_makefile_output build/CoqMakefile.make

# "clean::" occurs also in build/CoqMakefile.make, hence both colons
clean::
	rm -f .coq_makefile_input .coq_makefile_output .coq_makefile_output.conf build/CoqMakefile.make COQC.log
	find UniMath \( -name .\*.aux -o -name \*.glob -o -name \*.d -o -name \*.vo \) -delete
	find UniMath -type d -empty -delete
clean::; rm -rf $(ENHANCEDDOCTARGET)
latex-clean clean::; cd $(LATEXDIR) ; rm -f *.pdf *.tex *.log *.aux *.out *.blg *.bbl

distclean:: clean
distclean::          ; - $(MAKE) -C sub/coq distclean
distclean::          ; rm -f build/Makefile-configuration

#############################################################################
# building coq:
export PATH:=$(shell pwd)/sub/coq/bin:$(PATH)
CONFIGURE_OPTIONS := -coqide "$(COQIDE_OPTION)" -with-doc no -prefix $(shell pwd)
BUILD_TARGETS := coqbinaries tools states coq
ifeq ($(DEBUG_COQ),yes)
CONFIGURE_OPTIONS += -annot
BUILD_TARGETS += byte
BUILD_OPTIONS += VERBOSE=true
BUILD_OPTIONS += READABLE_ML4=yes
endif
ifeq ($(BUILD_COQIDE),yes)
BUILD_TARGETS += coqide-files bin/coqide
endif
sub/coq/configure.ml:
	git submodule update --init sub/coq
sub/coq/config/coq_config.ml: sub/coq/configure.ml
	@echo --- making $@ because of $?
	cd sub/coq && ./configure $(CONFIGURE_OPTIONS)
sub/coq/bin/coq_makefile sub/coq/bin/coqc: sub/coq/config/coq_config.ml
.PHONY: rebuild-coq
rebuild-coq sub/coq/bin/coq_makefile sub/coq/bin/coqc:
	$(MAKE) -w -C sub/coq $(BUILD_OPTIONS) $(BUILD_TARGETS)
	$(MAKE) -w -C sub/coq install
ifeq ($(DEBUG_COQ),yes)
	$(MAKE) -w -C sub/coq tags
endif
#############################################################################

git-describe:
	git describe --dirty --long --always --abbrev=40
	git submodule foreach git describe --dirty --long --always --abbrev=40 --tags
doc: $(GLOBFILES)
	mkdir -p $(ENHANCEDDOCTARGET)
	cp $(ENHANCEDDOCSOURCE)/proofs-toggle.js $(ENHANCEDDOCTARGET)/proofs-toggle.js
	$(SHOW)COQDOC
	$(HIDE)$(COQDOC)							\
	    -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d $(ENHANCEDDOCTARGET)	\
	    --with-header $(ENHANCEDDOCSOURCE)/header.html			\
	    $(VFILES)
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
	cd UniMath &&												\
	rm -f $(ISOLATED_BUG_FILE) &&										\
	../sub/coq-tools/find-bug.py --coqbin ../sub/coq/bin -R . UniMath					\
		--arg " -indices-matter"									\
		--arg " -type-in-type"										\
		--arg " -noinit"										\
		--arg " -indices-matter"									\
		--arg " -type-in-type"										\
		--arg " -w"											\
		--arg " -notation-overridden,-local-declaration,+uniform-inheritance,-deprecated-option"	\
		$(BUGGY_FILE) $(ISOLATED_BUG_FILE)
	@echo "==="
	@echo "=== the isolated bug has been deposited in the file UniMath/$(ISOLATED_BUG_FILE)"
	@echo "==="

world: all html doc latex-doc

latex-doc: $(LATEXDIR)/doc.pdf

$(LATEXDIR)/doc.pdf : $(LATEXDIR)/helper.tex $(LATEXDIR)/references.bib $(LATEXDIR)/latex-preamble.txt $(LATEXDIR)/helper.tex $(LATEXDIR)/latex-epilogue.txt
	cd $(LATEXDIR) && cat latex-preamble.txt helper.tex latex-epilogue.txt > doc.tex
	cd $(LATEXDIR) && latexmk -pdf -interaction=nonstopmode doc

$(LATEXDIR)/coqdoc.sty $(LATEXDIR)/helper.tex : $(VFILES:.v=.glob) $(VFILES)
	$(COQDOC) $(COQ_PATH) $(COQDOC_OPTIONS) $(COQDOCLATEXOPTIONS) $(VFILES) -o $@

.PHONY: check-max-line-length
check-max-line-length:
	LC_ALL="en_US.UTF-8" gwc -L $(VFILES) | grep -vw total | awk '{ if ($$1 > 100) { printf "%6d  %s\n", $$1, $$2 }}' | sort -r | grep .
show-long-lines:
	LC_ALL="en_US.UTF-8" grep -nE '.{101}' $(VFILES)

# here we assume the shell is bash, which it usually is nowadays, so we can get associative arrays:
SHELL = bash
check-prescribed-ordering: .check-prescribed-ordering.okay
clean::; rm -f .check-prescribed-ordering.okay

# The ordering check assumes Coq version ≥8.8, and gives up otherwise.  (Prior to 8.8, dependency files *.d were handled differently.)
VDFILE := ..coq_makefile_output.d
clean::; rm -f $(VDFILE)
ifeq ($(shell test -f build/CoqMakefile.make && grep -q ^VDFILE build/CoqMakefile.make && echo yes),yes)
# Coq >= 8.8
DEPFILES := $(VDFILE)
.check-prescribed-ordering.okay: Makefile $(DEPFILES) $(PACKAGE_FILES)
	@echo "--- checking the ordering prescribed by the files UniMath/*/.packages/files ---"
	@set -e ;														    \
	if declare -A seqnum 2>/dev/null ;											    \
	then n=0 ;														    \
	     for i in $(VOFILES) ;												    \
	     do n=$$(( $$n + 1 )) ;												    \
		seqnum[$$i]=$$n ;												    \
	     done ;														    \
	     for i in $(VFILES:.v=.vo);												    \
	     do grep "^$$i" $(DEPFILES) ;											    \
	     done														    \
	     | sed -E -e 's/[^ ]*\.(glob|v|vos|vok|required_vo|required_vos|v\.beautified)([ :]|$$)/\2/g' -e 's/ *: */ /'	    \
	     | awk NF \
	     | ( while read line ; \
	 	do \
		  for i in $$line ; do echo $$i ; done										    \
		  | ( read target ; 								    \
		      [ "$${seqnum[$$target]}" ] || (echo unknown target: $$target; false) >&2 ;				    \
		      while read prereq ;											    \
		      do \
			[ "$${seqnum[$$prereq]}" ] || (echo "unknown prereq of $$target : $$prereq" ; false) >&2 ;		    \
			(if [ "$${seqnum[$$prereq]}" -gt "$${seqnum[$$target]}" ] ; \
			 then echo "error: *** $$target should not require $$prereq" ; \
			 fi) ;\
		      done ) ;													    \
		done ) \
	     | ( haderror= ;													    \
		 while read line ;												    \
		 do haderror=$$(($$haderror+1)) ;								    \
		    echo "$$line" ;												    \
		 done ;														    \
		 [ ! "$$haderror" ] || (echo "$$haderror dependency order errors in package listings"; false))	;		\
	     touch $@ ;														\
	     echo "check succeeded: file dependency order follows package listings" ;						    \
	else echo "make: *** skipping checking the linear ordering of packages, because 'bash' is too old" ;			    \
	fi
else
DEPFILES := $(VFILES:.v=.v.d)
.check-prescribed-ordering.okay: Makefile $(DEPFILES) $(PACKAGE_FILES)
	@echo "make: *** skipping checking the linear ordering of packages, because Coq version is <8.8"
endif

# DEPFILES is defined above
$(DEPFILES): make-summary-files | build/CoqMakefile.make
	$(MAKE) -f build/CoqMakefile.make $@

# here we ensure that the travis script checks every package
check-travis:.check-travis.okay
clean::; rm -f .check-travis.okay
.check-travis.okay: Makefile .travis.yml
	@echo --- checking travis script ---
	@set -e ;													\
	for p in $(PACKAGES) ;												\
	do grep -q "PACKAGES=.*$$p" .travis.yml || ( echo "package $$p not checked by .travis.yml" >&2 ; exit 1 ) ;	\
	done
	touch "$@"


# here we ensure that every *.v file F in each package P is listed in the corresponding file UniMath/P/.package/files
# except for those listed in $GRANDFATHER_UNLISTED (currently none)
GRANDFATHER_UNLISTED = 
check-listing-of-proof-files:
	@ echo "--- checking every proof file is listed in one of the packages ---"
	@ if declare -A islisted 2>/dev/null ;										\
	  then for i in $(VFILES) $(GRANDFATHER_UNLISTED) ;								\
	       do islisted[$$i]=yes ;											\
	       done ;													\
	       m=0 ;													\
	       for P in $(PACKAGES) ;											\
	       do find UniMath/$$P -name '*.v' |									\
		       (												\
		       n=0 ;												\
		       while read F ;											\
		       do if [ "$${islisted[$$F]}" != yes ] ;								\
			  then echo "error: *** file $$F not listed in appropriate file UniMath/*/.package/files" >&2 ;	\
			       n=$$(( $$n + 1 )) ;									\
			  fi ;												\
		       done ; exit $$n ) ;										\
		  m=$$(( $$m + $$? )) ;											\
	       done ;													\
	       if [ $$m != 0 ] ;											\
	       then echo "error: *** $$m unlisted proof files encountered" >&2 ;					\
		    exit 1 ;												\
	       else echo "check succeeded: all proof files listed in packages" ;					\
	       fi ;													\
	  else echo "make: *** skipping checking the listing of proof files, because 'bash' is too old" ;		\
	  fi

# Here we check for changes to UniMath/Foundations, which normally does not change.
# One step of the travis job will fail if a change is made, see .travis.yml
check-for-change-to-Foundations:
	@echo "--- checking for changes to the Foundations package ---"
	git fetch origin
	test -z "`git diff --stat origin/master -- UniMath/Foundations`"
	@echo "check succeeded: no changes to Foundations"

# Here we check for changes to sub/coq, which normally does not change.
# One step of the travis job will fail if a change is made, see .travis.yml
check-for-submodule-changes:
	@echo "--- checking for submodule changes ---"
	git fetch origin
	test -z "`git diff origin/master sub`"
	@echo "check succeeded: no changes to submodules"

# Here we check that the CONTENTS.md file has been correctly updated,
# and committed if any changes have occurred.
# One step of the travis job will fail if there are outstanding changes, see .travis.yml
check-for-changes-to-CONTENTS.md : UniMath/CONTENTS.md
	@echo "--- checking that CONTENTS.md is up-to-date ---"
	test -z "`git diff UniMath/CONTENTS.md`"
	@echo "check succeeded: CONTENTS.md is up-to-date"

# Here we create a table of contents file, in markdown format, for browsing on github
# When the file UniMath/CONTENTS.md changes, the new version should be committed to github.
all: UniMath/CONTENTS.md
UniMath/CONTENTS.md: Makefile UniMath/*/.package/files
	$(SHOW)'--- making $@'
	$(HIDE) exec >$@ ;													\
	   echo "# Contents of the UniMath library" ;										\
	   echo "The packages and files are listed here in logical order: each file depends only on files occurring earlier." ;	\
	   for P in $(PACKAGES) ;												\
	   do if [ -f UniMath/$$P/README.md ] ;											\
	      then echo "## Package [$$P]($$P/README.md)" ;									\
	      elif [ -f UniMath/$$P/README ] ;											\
	      then echo "## Package [$$P]($$P/README)" ;									\
	      else echo "## Package $$P" ;											\
	      fi ;														\
	      for F in `<UniMath/$$P/.package/files $(FILES_FILTER)` ;								\
	      do echo "   - [$$F]($$P/$$F)" ;											\
	      done ;														\
	      echo "   - [All.v]($$P/All.v)" ;											\
	   done

# Here we call a shell script checking the Coq files for adherence to our style
check-style :
	util/checkstyle $(VFILES)

# Here we create the files UniMath/*/All.v, with * running over the names of the packages.  Each one of these files
# will "Require Export" all of the files in its package.
define make-summary-file
make-summary-files: UniMath/$1/All.v
UniMath/$1/.package/files: ;
UniMath/$1/All.v: UniMath/$1/.package/files
	$(SHOW)'--- making $$@'
	$(HIDE)																				\
	  exec > $$@ ;																			\
	  echo "(* This file has been auto-generated, do not edit it. *)" ;												\
	  <UniMath/$1/.package/files $(FILES_FILTER_2) | grep -v '^\(.*/\)\?Tests\?.v$$$$' |sed -e "s=^=Require Export UniMath.$1.=" -e "s=/=.=g" -e s/\.v$$$$/./
endef
$(foreach P, $(PACKAGES), $(eval $(call make-summary-file,$P)))

# Here we create the file UniMath/All.v.  It will "Require Export" all of the All.v files for the various packages.
make-summary-files: UniMath/All.v
UniMath/All.v: Makefile
	$(SHOW)'--- making $@'
	$(HIDE)									\
	exec > $@ ;								\
	echo "(* This file has been auto-generated, do not edit it. *)" ;	\
	for P in $(PACKAGES);							\
	do echo "Require Export UniMath.$$P.All.";				\
	done

# here we make the emacs local values file
all: UniMath/.dir-locals.el
UniMath/.dir-locals.el : UniMath/.dir-locals.el.in
ifeq ($(BUILD_COQ),yes)
	sed -e "s/@LOCAL@ //"   <$< >$@
else
	sed -e "s/@LOCAL@ /;;/" <$< >$@
endif
distclean::; rm -f UniMath/.dir-locals.el

# make *.vo files by calling the coq makefile
%.vo : always; $(MAKE) -f build/CoqMakefile.make $@
always:
.PHONY: always 

#################################
# targets best used with INCLUDE=no
git-clean:
	git clean -Xdfq
	git submodule foreach git clean -xdfq
git-deinit:
	git submodule foreach git clean -xdfq
	git submodule deinit -f sub/*
#################################
