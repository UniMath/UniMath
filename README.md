Univalent Mathematics
=====================

This coq library aims to formalize a substantial body of mathematics using the
univalent point of view.

## Contents

The "UniMath" subdirectory contains various packages of formalized
mathematics. Please see the file README (or README.md) in each package for more
information about its contents.

## Installation

Prepare for installation by installing the OCAML compiler on your system.
Under Mac OS X, the most convenient way to do that is with "Homebrew",
available from http://brew.sh/, with the following command:

```bash
$ brew install objective-caml
```

To download UniMath and prepare for building it, issue the following
shell commands.

```bash
$ git clone https://github.com/UniMath/UniMath
$ cd UniMath
```

To compile the coq formalizations (in all the packages), issue the following
shell commands (in this directory).

```bash
$ make
```

To create the documentation:
```bash
$ make html
```

To make a TAGS file for use with emacs "etags" commands:
```bash
$ make TAGS
```

To install UniMath in the "user-contrib" directory of coq, for use by other developments:
```bash
$ make install
```
The path to that directory from here, by default, is ./sub/coq/user-contrib/.

## Further details

The correct version of coq is built and used automatically by the command
"make".  If you wish to bypass the building of coq and use your own version,
then follow the instructions in the file build/Makefile-configuration.template.
In order to use the resulting coq programs from the command line or from
ProofGeneral (outside of "make") then add the full path for the directory
./sub/coq/bin to your "PATH" environment variable, or set the emacs variable
"coq-prog-name" in your emacs initialization file, ".emacs".

The various *.v files are compiled by coq in such a way that the fully
qualified name of each identifier begins with UniMath.  For example, the fully
qualified name of "maponpaths" in uu0.v is
"UniMath.Foundations.Generalities.uu0.maponpaths".

The preferred way to interact with the coq code is with ProofGeneral, running
in a modern version of emacs.  The file UniMath/.dir-locals.el will set the
emacs variable "coq-prog-args" appropriately.  In particular, it will add the
directory UniMath to the path, using the "-R" option.
