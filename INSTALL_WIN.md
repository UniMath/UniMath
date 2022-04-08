Running UniMath in Windows
==========================


---

These notes are copied verbatim from the report at https://github.com/UniMath/UniMath/issues/1351. They are recorded here for convenience, with permission of their author. You are very welcome to expand these notes and adapt them, if necessary. The UniMath maintainers cannot provide support for UniMath in Windows.

---



I helped someone with a minimal setup running UniMath on Windows inside VSCode, and wanted to quickly write down what worked for me. OCaml, Coq, and Emacs all run natively on Windows, so if you make it past the "make" step in Cygwin, everything should work one way or another from there.

This process was mostly trial an error, and far from perfect. In particular, you should only need one coq installation (I'm not really sure why UniMath builds its own anyway), and it would be much better to include the UniMath files in the correct path variable (it looks like this is setup with Emacs in this repository) rather than include them through the command line. Good luck!


## Install Coq through Cygwin
Followed directions [here](https://github.com/coq/platform/blob/2021.02.1/README_Windows.md) to install coq from source using cygwin.
This was probably overkill, but since the UniMath makefile builds coq from source, it seemed like a good setup and sanity check.

## Install UniMath
Inside cygwin, `git clone` UniMath and `make`.

(The makefile does let you specific BUILD_COQ=no, but I did not try this.)

There is now a second coq installation located at `path/to/UniMath/sub/coq/bin`.

E.g. in Cygwin you can run:

```$ path/to/UniMath/sub/coq/bin/coqtop.exe```

And test that coq is working.

## Include the UniMath files
At this point the UniMath library is not loaded, if you try to run

```Coq < Require Export UniMath.Foundations.Sets.```

You will get an error saying there is no physical path bound to the logical path

One way to fix this is to provide it at the command line. Run

```$ path/to/UniMath/sub/coq/bin/coqtop.exe -R "path/to/UniMath/UniMath" UniMath```

(See `coqtop --help`, the `-R` option recursively binds a physical folder to a logical folder)

Afterwhich the import should be resolved correctly:

```Coq < Require Export UniMath.Foundations.Set.```

At this point, I seem to be able to run UniMath files through the command line without issue.

## Visual Studio Code
The VSCoq plugin lets you point to the `path\to\UniMath\sub\coq\bin` (we're now outside cygwin, so this is a windows path, probably pointing to `C:\cygwin64_coq\home\user\UniMath`)
Change the name of the binaries to `coqtop.exe` and `coqidetop.exe` and finally pass in additional command line arguments to include the UniMath files. (Again the path is now a windows path.) (The arguments should be given as a three part list, not a single string.)
