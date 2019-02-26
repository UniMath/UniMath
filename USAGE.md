Using UniMath
=============


Browsing and editing a file
---------------------------
Once you have [installed](./INSTALL.md) UniMath, you can start browsing and editing the source files.
There are several programs to interactively edit and step through the files, among which
are [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) and [ProofGeneral](https://proofgeneral.github.io/).
Here, we focus on ProofGeneral.

During the [installation procedure](./INSTALL.md) you have set up ProofGeneral on your computer.
ProofGeneral is an add-on to the text editor Emacs, adding buttons, menus, and keyboard shortcuts
to interact with Coq, the proof assistant that UniMath relies on.

Upon opening a Coq file (i.e., a file with ending *.v) in Emacs, the ProofGeneral add-on is automatically
loaded by Emacs.
Andrej Bauer has a [screencast](https://www.youtube.com/watch?v=l6zqLJQCnzo) on using ProofGeneral
(more screencasts are listed on his [website](http://math.andrej.com/2011/02/22/video-tutorials-for-the-coq-proof-assistant/)).
Note that for Bauer's specific example to work in UniMath, you need to insert the line
```
Require Import Coq.Init.Prelude.
```
at the beginning of the file, since UniMath does not load this library by default.

*NB:* Emacs loads special settings to handle UniMath files. These settings are only loaded when
editing files in the subdirectory `UniMath/UniMath`.
To edit your own files with the same comfort, place them in this subdirectory.

Unicode input
-------------
Unicode symbols are used throughout UniMath. To see how to input a specific Unicode character, type
`M-x describe-char` while hovering over that character.

