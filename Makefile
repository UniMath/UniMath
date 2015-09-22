# Substsystems project makefile.
# Benedikt Ahrens, Ralph Matthes 2015 - 

# Quick usage: “make” to build core of library, “make all” to build all files.
# If you do not have Unimath installed globally, then invoke as e.g.
# make COQC="~/src/UniMath/sub/coq/bib/coqc"
# (or wherever you keep your UniMath coq).

# Modules to be compiled by default, in plain “make”.
# Includes everything that compiles in reasonable time, and all dependencies.
MODULES-CORE := Auxiliary \
		UnicodeNotations \
		AdjunctionHomTypesWeq  \
		HorizontalComposition \
		PointedFunctorsComposition \
		Signatures \
 		FunctorsPointwiseCoproduct \
		LamSignature \
		PointedFunctors \
		EndofunctorsMonoidal \
		FunctorsPointwiseProduct \
		ProductPrecategory \
		SumOfSignatures \
		ExampleSignatures \
		GenMendlerIteration \
		RightKanExtension \
		SubstitutionSystems_alt \
		MonadsFromSubstitutionSystems_alt \
		LiftingInitial_alt \
		Lam

	
# Remaining modules, included only in “make all”.
# Useful for leaves that are slow to recompile.
MODULES-EXTRA := 	MonadsFromSubstitutionSystems \
			FunctorAlgebraViews  \
			SubstitutionSystems \
			LiftingInitial 			

VS-CORE  := $(MODULES-CORE:%=%.v)
VS-EXTRA := $(MODULES-EXTRA:%=%.v)

COQDOC := coqdoc

PROJECTNAME="SubstSystems"

COQOPTIONS="-type-in-type"

COQDOCLATEXOPTIONS := -p "\usepackage{textgreek}\usepackage{stmaryrd}\DeclareUnicodeCharacter{10627}{{\(\llparenthesis\)}}\DeclareUnicodeCharacter{10628}{{\(\rrparenthesis\)}}"
LATEXDIR := latex
HTMLDIR := html

.PHONY: core all clean latexclean htmlclean

core: Makefile.coq
	$(MAKE) -f Makefile.coq 

all: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq 

Makefile.coq: Makefile $(VS-CORE)
	coq_makefile -R . $(PROJECTNAME) $(VS-CORE) -arg $(COQOPTIONS) -o Makefile.coq

Makefile_all.coq: Makefile $(VS-CORE) $(VS-EXTRA)
	coq_makefile -R . $(PROJECTNAME) $(VS-CORE) $(VS-EXTRA) -arg $(COQOPTIONS) -o Makefile_all.coq

install_all: core
	$(MAKE) -f Makefile_all.coq install

install: core
	$(MAKE) -f Makefile.coq install

clean:: Makefile_all.coq htmlclean latexclean
	$(MAKE) -f Makefile_all.coq clean
	rm -f Makefile_all.coq

htmlclean: 
	rm -rf $(HTMLDIR)

latexclean:
	rm -rf $(LATEXDIR)

html: core
	mkdir -p $(HTMLDIR) 
	$(COQDOC) -R . $(PROJECTNAME) -toc $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d $(HTMLDIR) $(VS-CORE) 

html_all: all
	mkdir -p $(HTMLDIR) 
	$(COQDOC) -R . $(PROJECTNAME) -toc $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d $(HTMLDIR) $(VS-CORE) $(VS-EXTRA)

latex: core
	mkdir -p $(LATEXDIR) 
	$(COQDOC) -R . $(PROJECTNAME) -toc $(COQDOCFLAGS) -utf8 $(COQDOCLATEXOPTIONS) -latex $(COQDOCLIBS) -d $(LATEXDIR) $(VS-CORE) 

pdf: latex	
	cd $(LATEXDIR) ;\
	latexmk -pdf *.tex


wc: Makefile
	coqwc $(VS-CORE)

wc_all: Makefile
	coqwc $(VS-CORE) $(VS-EXTRA)


# Makefile based on example from Adam Chlipala, “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html
