Installation of UniMath
=======================

Prepare for installation by installing the OCAML compiler and a more modern
version of `bash` on your system.

## Preparing for the installation under Mac OS

### First method (recommended for beginners)

Under Mac OS X, the most convenient way to
do that is with "Homebrew", available from http://brew.sh/, with the following
command:

```bash
$ brew install objective-caml camlp5 camlp4 lablgtk bash
```

Also install "ocamlfind" using "homebrew" with the following commands.

```bash
$ brew tap mht208/formal
$ brew install ocaml-findlib
```

Under Mac OS X, you may obtain ProofGeneral from http://proofgeneral.inf.ed.ac.uk/.
It comes with installation instructions.  Your version of emacs determines
which version of ProofGeneral you need, roughly, so some experimentation may be
required; you may even need the current development version if your emacs is
recent.

Now proceed with "Installing UniMath under Mac OS or Linux" below.

### Second method (allows more flexibility, but is more involved than first method)

Under Mac OS X, the most convenient way to do that is with "Homebrew",
available from http://brew.sh/, with the following command:

```bash
$ brew install bash opam gtk+
$ opam init --no-setup --compiler=4.02.3
$ opam install --yes lablgtk camlp5 ocamlfind
```

(We choose version 4.02.3 of ocamlc above, because it can successfully compile
Coq 8.6.1.)

Now arrange for the programs installed by opam to be available to the currently
running shell:

```bash
$ eval `opam config env`
```

If you haven't done it previously in connection with installing opam, as you
have just done, arrange for the programs (such as ocamlc) that opam will
install for you to be found by your shell, the next time you log in, by adding
the line

```bash
$ eval `opam config env`
```

to your file `~/.profile`, after any lines in the file that add
`/usr/local/bin` to the `PATH` environment variable.  (Homebrew and opam both
know how to install `ocamlc`, and we intend to use `opam` to get a version of
`ocamlc` appropriate for compiling the version of Coq used by UniMath.)

The next time you log in, or now, you may check that the progams installed by
opam are accessible by you as follows.

```bash
$ type ocamlc
ocamlc is hashed (/Users/XXXXXXXX/.opam/4.02.3/bin/ocamlc)
$ ocamlc -version
4.02.3
$ camlp5 -v
Camlp5 version 7.03 (ocaml 4.02.3)
```

Under Mac OS X, you may obtain ProofGeneral from http://proofgeneral.inf.ed.ac.uk/.
It comes with installation instructions.  Your version of emacs determines
which version of ProofGeneral you need, roughly, so some experimentation may be
required; you may even need the current development version if your emacs is
recent.


## Preparing for the installation under Linux

Under Ubuntu or Debian, you may install ocaml (and ProofGeneral) with

```bash
$ sudo apt-get install build-essential git ocaml ocaml-nox ocaml-native-compilers camlp4-extra camlp5 proofgeneral proofgeneral-doc libgtk2.0 libgtksourceview2.0 liblablgtk-extras-ocaml-dev ocaml-findlib
```

## ProofGeneral add-ons

Some useful ProofGeneral add-ons are available for installation at https://github.com/cpitclaudel/company-coq

## Installing UniMath under Mac OS or Linux

To download UniMath and prepare for building it, issue the following
shell commands.

```bash
$ git clone https://github.com/UniMath/UniMath
$ cd UniMath
```

To compile the Coq formalizations (in all the packages), issue the following
shell command (in this directory).

```bash
$ make
```

To compile an individual package and the files it depends on, e.g., the package `CategoryTheory`, issue
```bash
$ make CategoryTheory
```

To compile an individual file and the files it depends on, e.g., the file `CategoryTheory/Categories.v`, issue
```bash
$ make UniMath/CategoryTheory/Categories.vo
```
Note the extension `*.vo` required in the command.

If you wish also to build the program ```coqide```, then issue the following
command instead of the one above.

```bash
$ make BUILD_COQIDE=yes
```

Alternatively, you can specify the value of the BUILD_COQIDE option more
permanently by following the instructions in the file
build/Makefile-configuration-template.

Later on, after running the command `make install` as instructed below, in
order to run the program ```coqide```, you may use the following command.

```bash
$ sub/coq/bin/coqide -indices-matter -type-in-type -Q UniMath UniMath
```

To create the standard HTML documentation provided by coqdoc:
```bash
$ make html
```
The documentation is created in the subdirectory ```html```.

To create HTML documentation with "hidden" proofs:
```bash
$ make doc
```
In this version of the documentation, any proof enclosed within ```Proof.``` and ```Qed.```/```Defined.``` is replaced by a button ```Show proof.```.
Clicking on this button unveils (unfolds) the corresponding proof. A ```Hide proof``` button can be used to fold the proof again.
The documentation is created in the subdirectory ```enhanced-html```.
(This feature requires the use of the otherwise optional ```Proof``` command of
the Coq vernacular language to indicate the beginning of the proof.  Toggling
of proofs requires an internet connection for downloading the ```jquery```
library.)

To install UniMath in the ```user-contrib``` directory of Coq, for use by other developments:
```bash
$ make install
```
The path to that directory from here, by default, is ./sub/coq/user-contrib/.

## TAGS files

Emacs (which every UniMath user should become expert with) includes a facility
called "tags" which enables easy navigation between Coq proof files.  For
example, you may be examining a proof containing a reference to a symbol such
as "has_homsets", and you may wonder where the source code of its definition
is.  To do that, one positions the cursor on the symbol, presses ```M-.```,
accepts (or modifies) the proffered string, and presses return.  Emacs then
takes you to the source code of the definition.  One may repeat that as often
as desired, and return one level upward in the chain of locations visited with
```M-*```.

In order to enable this facility, make a "TAGS" file as follows.
To make a TAGS file for use with emacs ```etags``` commands:
```bash
$ make TAGS
```
To make a TAGS file dealing with a single package, for example, ```Foundations```:
```bash
$ make TAGS-Foundations
```

The first time the tags facility is used, the user will be prompted for the
location of a TAGS file to use -- it will be in the top-level directory of
UniMath.

## Measuring compilation time

To obtain information about the compilation time of each file, add
```TIMED=yes``` to the ```make``` command line.  For this to work, you need the
GNU ```time``` utility installed on your system in ```/usr/bin```.  Alternatively,
add ```TIMECMD=time``` to the ```make``` command line, where ```time``` is a
time command that works on your system.

On both Linux and Mac OS X systems, ```time``` is a built in bash shell command
that differs from GNU time, available on Linux systems as ```\time```.  Under
Mac OS X, you can install GNU time as ```gtime``` by running ```brew install
gnu-time```.

Since ```make``` variables can be included in the time command, the following
example (using GNU time ```gtime```) shows how to display the user time and the name of the
file on the same line.
```
$ time make TIMECMD='gtime -f "user time %U: $*"'
```
The first ```time``` command provides overall time for the whole build.

Timing of execution of individual tactics and vernacular commands can be obtained by
```bash
$ make MOREFLAGS=-time
```
For postprocessing of the (huge) output, use our utility ```slowest```, like this:
```bash
$ make MOREFLAGS=-time TIMECMD='util/slowest 10 0.5'
```
For each Coq file compiled, the timing of the 10 slowest steps taking at least
0.5 seconds will be displayed.

You may time both steps and files like this:
```bash
$ make MOREFLAGS=-time TIMECMD='gtime -f "user time %U: $(basename $*)" util/slowest 10 0.5'
```

To speed up execution on a machine with multiple cores or pseudo-cores, specify
the use of multiple processes in paralle, e.g, 4, as follows.
```
$ make -j4
```

## Further details

The correct version of Coq is built and used automatically by the command
```make```.  (If you wish to bypass the building of Coq and use your own version,
then follow the instructions in the file build/Makefile-configuration-template.)

The file ```UniMath/.dir-locals.el``` contains code that arranges for
ProofGeneral to use the Coq programs built by ```make``` when one of the proof
files of UniMath is opened in emacs; in order to use them more generally, such
as from the command line,, then add the full path for the directory
```./sub/coq/bin``` to your ```PATH``` environment variable, or set the emacs
variable ```coq-prog-name``` in your emacs initialization file, ```.emacs```.

The various *.v files are compiled by Coq in such a way that the fully
qualified name of each identifier begins with UniMath.  For example, the fully
qualified name of ```maponpaths``` in uu0.v is ```UniMath.Foundations.Basics.PartA.maponpaths```.

The preferred way to interact with the Coq code is with ProofGeneral, running
in a modern version of emacs.  The file UniMath/.dir-locals.el will set the
emacs variable ```coq-prog-args``` appropriately.  In particular, it will add the
directory UniMath to the path, using the ```-R``` option, and it will arrange for
files with names of the form ```*.v``` to be edited in "Coq mode".

We are using some unicode characters in our Coq files.  One way to type such
characters easily is with the "Agda input method": to type σ, for example, one
types \sigma, which is automatically replaced by σ.  We have arranged for the
Agda input method to be automatically enabled in buffers containing one of the
UniMath Coq files.  The emacs command for viewing the typing shortcuts offered
by the Agda input method is ```C-H I```.

## Problems

In this section we describe some problems that have been encountered during compilation, and how to fix them.

### Errors while compiling Coq

The following type mismatch error during compilation of Coq results from a mismatch
between the version of Ocaml used and the version of Coq being compiled.

```
"/usr/local/bin/ocamlfind" opt -rectypes -dtypes -w -3-52-56  -I config -I lib -I kernel -I kernel/byterun -I library -I proofs -I tactics -I pretyping -I interp -I stm -I toplevel -I parsing -I printing -I intf -I engine -I ltac -I tools -I tools/coqdoc -I plugins/omega -I plugins/romega -I plugins/micromega -I plugins/quote -I plugins/setoid_ring -I plugins/extraction -I plugins/fourier -I plugins/cc -I plugins/funind -I plugins/firstorder -I plugins/derive -I plugins/rtauto -I plugins/nsatz -I plugins/syntax -I plugins/decl_mode -I plugins/btauto -I plugins/ssrmatching -I plugins/ltac -I "/usr/local/Cellar/camlp5/7.03_1/lib/ocaml/camlp5" -thread -g    -c lib/pp_control.ml
File "lib/pp_control.ml", line 61, characters 22-33:
Error: This expression has type bytes -> int -> int -> unit
       but an expression was expected of type string -> int -> int -> unit
       Type bytes is not compatible with type string 
```

For example, Coq 8.6.1 cannot be compiled by Ocaml 4.06.0, and must instead be
compiled by an older version.  In the instructions above, we arrange for Ocaml
4.02.3 to be used to compile Coq 8.6.1.

### Problems caused by ill-formed input to make

When calling ```make```, various files are read, some of them not under version control by git. 
If those files are ill-formed, ```make``` stops working; in particular, ```make``` cannot be used to delete and recreate those files.
When such a situation arises, one solution is to try cleaning everything with this command:
```bash
$ make INCLUDE=no distclean
```
Another solution is to let git do the cleaning, by running:
```bash
$ git clean -Xdfq
$ git submodule foreach git clean -Xdfq
```
The Makefile provides this pair of commands, too:
```bash
$ make INCLUDE=no git-clean
```

### Problems specific to MacOS

If you get error messages involving the command line option ```-fno-defer-pop```, you
might be running Mac OS X 10.9 with an ocaml compiler installed by ```brew```.  In
that case try

```bash
brew update
brew upgrade objective-caml
```

If that doesn't work, try

```bash
brew remove objective-caml
brew install objective-caml
```

### Problems specific to Linux (e.g., Debian and Ubuntu)

If you get the error message ```Error: cannot find 'ocamlc.opt' in your path!```, you need to install ocaml-native-compilers, e.g., by running
```bash
$ sudo apt-get install ocaml-native-compilers
```
This package is not among the build dependencies for older versions of Coq.
