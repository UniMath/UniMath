FOLDS
=====

Formalizing categories in FOLDS (First Order Logic with Dependent Sorts)

# Installation

1. Installation of the UniMath library
  ```
  $ git clone https://github.com/UniMath/UniMath.git
  $ cd UniMath
  $ make all   # installs Coq locally in sub/coq/bin and compiles the libraries mentioned in 1) above
  $ make install   # installs Coq vo files so that they are found when compiling FOLDS
```
2. Add UniMath/sub/coq to your PATH variable 

3. Compilation of the FOLDS library
  ```
  $ git clone https://github.com/benediktahrens/folds.git
  $ cd folds/coq
  $ make
  ```


