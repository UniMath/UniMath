Univalent Mathematics
=====================

This Coq library aims to formalize a substantial body of mathematics using the
[univalent point of view](https://en.wikipedia.org/wiki/Univalent_foundations).
It is licensed for use under the terms in the file ```LICENSE.md```.

## Contents

The "UniMath" subdirectory contains various packages of formalized
mathematics. Please see the file README (or README.md) in each package for more
information about its contents.

Some articles describing the contents of UniMath are listed in the 
[wiki](https://github.com/UniMath/UniMath/wiki/Documentation:-Articles-describing-UniMath).

## Installation

Prepare for installation by installing the OCAML compiler on your system.
Under Mac OS X, the most convenient way to do that is with "Homebrew",
available from http://brew.sh/, with the following command:

```bash
$ brew install objective-caml camlp5 camlp4 lablgtk
```

Under Ubuntu or Debian, you may install ocaml (and ProofGeneral) with

```bash
$ sudo apt-get install ocaml ocaml-nox ocaml-native-compilers camlp4-extra proofgeneral proofgeneral-doc libgtk2.0 libgtksourceview2.0
```

Under Mac OS X, you may obtain ProofGeneral from http://proofgeneral.inf.ed.ac.uk/.
It comes with installation instructions.  Your version of emacs determines
which version of ProofGeneral you need, roughly, so some experimentation may be
required; you may even need the current development version if your emacs is
recent.

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

If you wish also to build the program ```coqide```, then issue the following
command instead of the one above.

```bash
$ make BUILD_COQIDE=yes
```

Alternatively, you can specify the value of the BUILD_COQIDE option more
permanently by following the instructions in the file
build/Makefile-configuration-template.

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
(This feature requires the use of the otherwise optional ```Proof.``` vernacular to indicate the beginning of the . 
Toggling of proofs requires an internet connection for downloading the jquery library.)

To make a TAGS file for use with emacs ```etags``` commands:
```bash
$ make TAGS
```

To install UniMath in the ```user-contrib``` directory of Coq, for use by other developments:
```bash
$ make install
```
The path to that directory from here, by default, is ./sub/coq/user-contrib/.

### Measuring compilation time

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
example (using GNU time) shows how to display the user time and the name of the
file on the same line.
```
$ time make TIMECMD='\time -f "user time %U: $*"'
```
The first ```time``` command provides overall time for the whole build.

Timing of execution of individual tactics and vernacular commands can be obtained by
```bash
$ make MOREFLAGS=-time
```
For postprocessing of the (huge) output, direct the output into a file as in
```bash
$ make MOREFLAGS=-time > timing.txt
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

### MacOS

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

### Linux (e.g., Debian and Ubuntu)

If you get the error message ```Error: cannot find 'ocamlc.opt' in your path!```, you need to install ocaml-native-compilers, e.g., by running
```bash
$ sudo apt-get install ocaml-native-compilers
```
This package is not among the build dependencies for older versions of Coq.

Contributing to UniMath
=======================

To contribute to UniMath, submit a pull request or contact us.  Your code will
be subject to the copyright and license agreement in the file ```LICENSE.md```.

The UniMath Development Team
============================

The members of the UniMath Development Team are Vladimir Voevodsky, Benedikt
Ahrens, and Daniel Grayson.
