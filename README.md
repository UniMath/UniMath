# UniMath

By Vladimir Voevodsky February 2010 -- April 2014.

This is the April 2014 version of the mathematical library for the proof assistant Coq
based on the univalent semantics for the calculus of inductive constructions.

## Prerequisites

To compile the library you have to first compile Coq 8.4pl3 patched with the patch file
from `Coq_patch` subdirectory. See the `README.md` file in `Coq_patch` for further
instructions on how to compile the patched Coq and how to set up your `PATH` to make the
compiled binaries available.

You will also need the `make` utility, but you need that already to compile Coq.

We provide instructions on how to use the library with [Emacs](http://www.emacswiki.org/)
and [ProofGeneral](http://proofgeneral.inf.ed.ac.uk/). Thus we assume basic familiarity
with ProofGeneral. It may be possible to use other Coq interfaces, but we have not
investigated them.

## Compilation

Assuming the correct version of patched Coq 8.4pl3 is available on the `PATH` (see
previous section), the easiest way to compile the library is by typing

    make

in the main directory (where this `README.md`) file is. The library takes about one coffee
break to compile.

## Installation

If you type

    make install

the compiled library will be installed in the `user-contrib` directory of the version of
Coq that was used for compilation.

## How to use the library

Once the library is compiled the individual files of the library can be followed
line-by-line using an interface to Coq, such as [Proof
General](http://proofgeneral.inf.ed.ac.uk/). We assume you already have a working Emacs
with Proof General set up.

The only bit of customization needed is to tell Proof General that is should use the
patched Coq. There are two cases:

1. The `proof-prog-name-ask` variable is set to `t` and so Proof General always asks
   interactively which `coqtop` executable it should use. In this case point it to
   the `coqtop` executable from the patched Coq `coq-8.4pl3-uf`. You should still
   customize `coq-prog-args` by adding the `-no-sharing` option, so maybe the second
   case is better:

2. The `prof-prog-name-ask` variable is set to `nil` and Proof General uses the `coqtop`
   provided in the `coq-prog-name` variable. In this case you should set the variable
   to the `coqtop` executable from the patched Coq. You should also set
   `coq-prog-args` to `("-emacs-U" "-no-sharing")`.

The customization of Emacs variables can be accomplished through "Customize options" in
the Proof-General menu. To customize a specific variable, say `coq-prog-name`, type `M-x
customize-variable coq-prog-name RET`.

Once you have the Proof General running correctly.

## Generating the HTML files for browsing

You may generate an HTML version of the files suitable for browsing by typing

    make html

The files will be generated in the `html` subdirectory. The main file is called `index.html`.


## Description of files

The library contains the following subdirectories:

* `Generalities`
* `hlevel1`
* `hlevel2`
* `Proof_of_Extensionality`

### Directory `Generalities`

This directory contains the files `uuu.v` and `uu0.v`.

* File `uuu.v` contains some new notations for the constructions defined in `Coq.Init`
  library as well as the definition of "dependent sum" `total2`.

* File `uu0.v` contains the bulk of general results and definitions about types which are
  pertinent to the univalent approach. In this file we prove main results which apply to
  all types and which require only one universe level to be proved. Some of the results in
  `uu0` use the extensionality axiom for functions (introduced in the same file). No other
  axioms or resizing rules (see below) are used and these files should compile with the
  unpatched version of Coq-8.4.

### Directory `hlevel1`

This directory contains one file `hProp.v` with results and constructions related to types
of h-level 1 i.e. to types which correspond to "propositions" in our formalization. Some
of the results here use " resizing rules " and therefore it will currently not compile
without a `type_in_type` patch. Note that we continue to keep track of universe levels in
these files "by hand" and use only those "universe re-assignment" or "resizing" rules which
are semantically justified. Some of the results in this file also use the univalence axiom
for hProp called `uahp` which is equivalent to the axiom asserting that if two
propositions are logically equivalent then they are equal.

### Directory `hlevel2`

This directory contains files with constructions and results related to types of hlevel 2
i.e. to types corresponding to sets in our formalization.

* The first file is `hSet.v`. It contains most general definitions related to sets
  including the constructions related to set-quotients of types.

* The next group of files in the hierarchy are `algebra1{a,b,c,d}.v` which contains many
  definitions and constructions of general abstract algebra culminating at the moment in
  the construction of the field of fractions of an integral domain with decidable
  equality. The files also contain definitions and results about the relations on
  algebraic structures.

* The next file is `hnat.v` which contains many simple lemmas about arithmetic and
  comparisons on natural numbers.

* Then the hierarchy branches:

     * On one branch there are files `stnfsets.v` and `finitesets.v` which introduce
       constructions related to standard and general finite sets respectively.

     * On another branch there are files `hz.v` and `hq.v` which introduce the basic
       cosntructions related to the integer and rational arithmetic as particular cases of
       the general theorems of the algebra1 group of files.

  At the end of files `finitesets.v`, `hz.v` and `hq.v` there are sample computations
  which show that despite our use of the extensionality axioms the relevant terms of types
  `bool` and `nat` fully normalize. The last computation example in `hq.v` which evaluates
  the absolute value of the integral part of `10 / -3`.

### Directory `Proof_of_Extensionality`

This directory contains the formulation of general Univalence Axiom and a proof that it
implies functional extensionality.
