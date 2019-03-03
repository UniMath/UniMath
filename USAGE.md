Using UniMath
=============


Browsing and editing a file in the UniMath source tree
------------------------------------------------------

The UniMath library consists of Coq source files (file ending *.v) in the subdirectory `UniMath/UniMath`.

Once you have [installed](./INSTALL.md) UniMath, you can start browsing and editing the source files.
There are several programs to interactively edit and step through the files, among which
are 
1. [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) and 
2. Emacs with the [ProofGeneral](https://proofgeneral.github.io/) add-on.

Here, we focus on Emacs/ProofGeneral.

Automatic setup of work environment using Emacs
-----------------------------------------------

When opening a source file in the directory `UniMath/UniMath` in Emacs, the following happens **automatically**:
1. *The ProofGeneral add-on to Emacs is loaded.*
   ProofGeneral is an add-on to the text editor Emacs, adding buttons, menus, and keyboard shortcuts
   to interact with Coq, the proof assistant that UniMath relies on.
   During the [installation procedure](./INSTALL.md) you have set up ProofGeneral on your computer.
2. *A Unicode input method is loaded.* 
   It allows you to insert Unicode symbols using a LaTeX-like syntax.
   See [Section on Unicode input below](USAGE.md/#unicode-input)
3. ProofGeneral is informed about the location of the Coq proof assistant installed during the installation of UniMath,
   and of the options that need to passed to Coq.

Items 2 and 3 are achieved through the Emacs configuration file [`.dir-locals.el`](./UniMath/.dir-locals.el) located in 
the subdirectory `UniMath/UniMath`.
For this reason, we recommend you save your UniMath files in this subdirectory as well.


Stepping through a Coq file in Emacs/ProofGeneral
-------------------------------------------------
Andrej Bauer has a [screencast](https://www.youtube.com/watch?v=l6zqLJQCnzo) on using Emacs/ProofGeneral
for writing and stepping through a Coq file.
(More screencasts are listed on his [website](http://math.andrej.com/2011/02/22/video-tutorials-for-the-coq-proof-assistant/).)
For following his instructions using his example, we recommend you save the Coq file in the subdirectory `UniMath/UniMath`
to profit from the automatic setup mentioned above.
Note that for Bauer's specific example to work in UniMath, you need to insert the line
```
Require Import Coq.Init.Prelude.
```
at the beginning of the file, since the setup above does not load this library by default when reading a file.


Unicode input
-------------
Unicode symbols are used throughout UniMath. To see how to input a specific Unicode character, type
`C-u C-x =` (meaning: hold CTRL, then press u and x; release CTRL, press =) while hovering over that character.

Below is a partial list of Unicode symbols used in UniMath.

| Mathematical symbol | UniMath Unicode |UniMath ASCII |
|---------------------|-----------------|-----------------|
|  ∏ (x : A), B       | `\prod`          | `forall x : A, B`      |
| A → B               | `\to`            | `A -> B`  |
|  λ x, e             | `\lambda`          | `fun x => e`  |
| ∑ (x : A), B        | `\sum`         | `total2 (fun x => B)` |
|  X × Y              | `\times`       | `dirprod X Y` |
|  (a,b)              |                | `a,,b`|
| X ⨿ Y               | `C-X 8 RET AMALGAMATION OR COPRODUCT`| `coprod`|
| a = b               |             | `a = b`  |


