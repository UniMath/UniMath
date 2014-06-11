# Installation of patched Coq 8.4pl3

We start with instructions on how to generate Coq binaries which are needed to work with
this version of Foundations library. The information on the history and content of the
patch file is in the second part of this file.

These instructions were verified to work on OSX and Linux Debian. It is probably possible
to compile the library under Microsoft Windows using the Cygwin environment

## Prerequisites

You need standard developer tools `make` and `patch`. These are either installed on your
system or easily available through a package manager, such as [Homebrew](http://brew.sh/)
on OSX.

You need the OCaml compiler version 4 or later. Again, check your package manager for availability or consult the [OCaml web page](http://ocaml.org/).

## Instalation

To generate the Coq binaries follow these steps:

1. Open a terminal window and `cd` to main Foundation directory

       cd <LocationOfFoundationsDirectory>

   where `<LocationOfFoundationsDirectory>` is the location of the
   Foundations library.

2. Download the sources of Coq-8.4pl3 from

        http://coq.inria.fr/distrib/8.4pl3/files/coq-8.4pl3.tar.gz

   and unpack them into directory `coq-8.4pl3-uf` (if you do not have `wget`
   use a browser):

        wget http://coq.inria.fr/distrib/8.4pl3/files/coq-8.4pl3.tar.gz
        tar xfz coq-8.4pl3.tar.gz
        mv coq-8.4pl3 coq-8.4pl3-uf

   This directory should in particular contain the `Makefile` which comes with the
   sources.

3. Apply the patch:

        cd coq-8.4pl3-uf
        patch -p1 < ../Coq_patch/coq-8.4-ufpatches.diff

4. Compile Coq (continuing to work in `coq-8.4pl3-uf`):

        ./configure -coqide no -opt -with-doc no -local
        make GOTO_STAGE=2 coqbinaries states

    This will create a minimalistic installation of Coq sufficient for this library. To
    get other "standard library" files which come with Coq use `make` instead of `make
    GOTO ...` above.

    The Coq binary files are now in `coq-8.4pl3-uf/bin/`.
    
    If you are planning to generate the HMTL version of the Coq files (good idea),
    you should also type
    
        make bin/coqdoc

5. Add `coq-8.4pl3-uf/bin/` to your `PATH` variable of the shell where coq will be called
   from. In a Bourne style shell this is done by

        export PATH=<FoundationsDirectory>/coq-8.4pl3-uf/bin:$PATH

   where you replace `<FoundationsDirectory>` with the *absolute path* to the Foundations
   directory. You can also permanently add the directory to your path by adding the line
   above to `.profile` in your home directory.
   
6. To test that things worked well one may type

        coqc -v

   which should generate something like this:

        The Coq Proof Assistant, version 8.4pl3 (April 2014)
        compiled on Apr 24 2014 18:25:32 with OCaml 4.01.0

   with the date and time being the date when you ran make in dircoqpatched. 

## Description of the Coq patch

The patch file in this directory was created by Dan Grayson by combining together several
earlier patch files written by Dan Grayson and Hugo Herbelin. The following description is
from the earlier version where these patch files where separate:

Hugo's patches `inductive-indice-levels-matter-8.3.patch` and `patch.type-in-type` are
intended only as a temporary solution for the universe management issues in Coq which
arise in connection with the univalent approach.

The first of these patches changes the way the universe level of inductive types is
computed for those definitions which do not specify `Set` or `Prop` as the target of the
inductive construction explicitly. The new computation rule for the universe level takes
into account not only the universe levels of the types occurring in the constructors but
also the universe levels of types occurring in "pseudo-parameters", i.e., in the `forall`
expressions in the type of the inductive definition. For example, in the definition:

    Inductive Ind ( a1 : A1 ) : forall a2 : A2 , Type := ...

The universe level of `Ind` will be the maximum of the universe level computed on the
basis of types occurring in the constructors and the universe level of `A2`. The
universe level of `A1` which the type of a parameter `a1` (as opposed to a
pseudo-parameter `a2) is not taken into account.

The second patch switches off the universe consistency checking in Coq which is a
temporary measure which allows us to formalize interesting constructions such as `ishinh`
and `setquot` without having the resizing rules.

Dan's patches have the following functions (see also comments in the individual patches):

1. `grayson-closedir-after-opendir.patch` improves the management of file openings/closing
   and eliminates in most cases the complaint that there are too many open files (this has
   now been included in the standard Coq).

2. `fix-hanging-at-end-of-proof.patch` if I understand correctly, this is a temporary fix
   for a bug in the current version of Coq's "sharing" version of the normalization
   algorithm. The patch uses a flag previously installed in the source code to switch off
   some optimization features of the algorithm. The need for this patch arose because of
   several cases when Coq process would hang after `Admitted`. In practice the patch
   prevents hangings but makes compilation of some of the code slower. In particular, with
   this patch installed the current standard library file `Cycllic31.v` does not compile
   in a reasonable amount of time (see the suggestion of how to compile Coq without much
   of the standard library below). It also affect the time of compilation for some of the
   "computation tests" in the Foundations library increasing the compilation time by a
   factor of >5. Hopefully, the actual bug will be located and removed in the next update.
   (This has not been fixed as of Apr. 2014 but the behavior can now be controlled by the
   `-no-sharing` flag).

3. `grayson-improved-abstraction-version2-8.3pl2.patch` this patch dramatically improves
   the behavior of the `destruct` tactic making it applicable in many the cases when
   dependencies are present. It is not creating any complicated proof terms but simply
   uses the eliminator for inductive definitions in a more intelligent way than the
   standard `destruct` (this has now been included in the standard Coq).

4. `grayson-fix-infinite-loop.patch` fixes another hanging situation by terminating a
   certain tactic involving nested quantified hypotheses after 10 attempts.
