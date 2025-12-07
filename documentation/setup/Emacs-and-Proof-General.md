
Browsing and editing a file in the UniMath source tree
------------------------------------------------------

The UniMath library consists of Coq source files (file ending *.v) in the subdirectory `UniMath/UniMath`.

Once you have [installed](./Install.md) UniMath, you can start browsing and editing the source files.
There are several programs to interactively edit and step through the files, among which
are
1. [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) and
2. Emacs with the [Proof General](https://proofgeneral.github.io/) add-on.

Here, we focus on Emacs/Proof General.

Automatic setup of work environment using Emacs
-----------------------------------------------

When first opening a file in `UniMath/UniMath`, you will be asked to apply a list of local variables, similar to the screenshot below. To accept permanently and not be asked again, type "!". These variables are needed to achieve the automatic setup described below.
![Screenshot Emacs](https://raw.githubusercontent.com/wiki/UniMath/UniMath/Screenshot_Emacs.png)

When opening a source file in the directory `UniMath/UniMath` in Emacs, the following happens **automatically**.
1. *The Proof General add-on to Emacs is loaded.*
   Proof General is an add-on to the text editor Emacs, adding buttons, menus, and keyboard shortcuts
   to interact with Coq, the proof assistant that UniMath relies on.
   During the [installation procedure](./Install.md) you have set up Proof General on your computer.
2. *A Unicode input method is loaded.*
   It allows you to insert Unicode symbols using a LaTeX-like syntax.
   See [the page on Unicode input below](../unimath/Symbols-list.md).
3. Proof General is informed about the location of the Coq proof assistant installed during the installation of UniMath,
   and of the options that need to be passed to Coq.

Items 2 and 3 are achieved through the Emacs configuration file [`.dir-locals.el`](../../UniMath/.dir-locals.el) located in
the subdirectory `UniMath/UniMath`.
For this reason, we recommend you save your UniMath files in this subdirectory as well.


Stepping through a Coq file in Emacs/Proof General
-------------------------------------------------
Andrej Bauer has a [screencast](https://www.youtube.com/watch?v=l6zqLJQCnzo) on using Emacs/Proof General
for writing and stepping through a Coq file.
(More screencasts are listed on his [website](http://math.andrej.com/2011/02/22/video-tutorials-for-the-coq-proof-assistant/).)
For following his instructions using his example, we recommend you save the Coq file in the subdirectory `UniMath/UniMath`
to profit from the automatic setup mentioned above.
Note that for Bauer's specific example to work in UniMath, you need to insert the line
```
Require Import Coq.Init.Prelude.
```
at the beginning of the file, since the setup above does not load this library by default when reading a file.

Various special commands for dealing with proof scripts are bound to keys in Proof General's proof mode.
To get a list of such key bindings, type ` C-h f proof-mode RETURN `.

# TAGS
Tags in emacs is a convenient way for searching or replacing names throughout a development. To compile the TAGS file write:

``make TAGS``

and then to do a tags replace type `M-R` (or follow buttons in emacs: Edit -> Replace -> Replace in Tagged Files). For more information see:

https://www.gnu.org/software/emacs/manual/html_node/emacs/Tags.html

# Cheat sheet

Coq Proof General supplies the following key-bindings:

    C-c C-a C-i
    Inserts “Intros ”

    C-c C-a C-a
    Inserts “Apply ”

    C-c C-a C-s
    Inserts “Section ”

    C-c C-a C-e
    Inserts “End <section-name>.” (this should work well with nested sections).

    C-c C-a C-o
    Prompts for a SearchIsos argument.

    C-c C-a C-n
    Locate "<notation>".

    C-x v g
    Calls "git blame".
