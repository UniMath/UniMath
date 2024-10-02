The Linux distribution "Springdale Linux" that runs on the IAS office computers comes with a too old OCaml version (3.11) to compile Coq. Instead, Dan Grayson installed a more recent version of OCaml in a shared directory.
We use this directory as a source of standard software for use with
formalization of proofs using the Univalent Foundations of Voevodsky.

All the files are in the subdirectory called ```usr```.  To use them:

1. add the following lines to ~/.profile or ~/.bashrc:
 ```
 export PATH=/home/special/univalence/usr/bin:$PATH
 export MANPATH=/home/special/univalence/usr/man:$MANPATH
 ```
 Use 
 ```
 $ echo $PATH
 ```
 to check that it works: the directory ```/home/special/univalence/usr/bin``` should be among those listed by this command.

2. add the following lines to ~/.emacs:
 ```
 (setq load-path (append
 '("/home/special/univalence/usr/share/emacs/site-lisp") load-path))
      (load "ProofGeneral/generic/proof-site")
 ```