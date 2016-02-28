Univalent Mathematics Coq files
===============================

Each subdirectory of this directory consists of a separate package, with
various authors, as recorded in the README (or README.md) file in it.

## Adding a file to a package

Each package contains a subdirectory called ".package".  The file
".packages/files" consists of a list of the paths to the *.v files of the
package, in order, i.e., a file is listed after files it depends on.
(That's just so the TAGS file will be correctly sequenced.)  To add a file to a
package, add its path to that file.

## Adding a new package

Create a subdirectory of this directory, populate it with your files, add a
README (or README.md) file, and add a file .packages/files, listing the *.v
files of your package, as above.  Then add the name of your package to the head
of the list assigned to "PACKAGES" in the file "./Makefile", or, alternatively,
if you'd like to test your package with modifying "./Makefile", which you might
accidentally commit and push, add its name to the head of the list in
"../build/Makefile-configuration", which is created from
"../build/Makefile-configuration-template".

## UniMath coding style

We purposely restrict our use of Coq to a subset whose semantics is more likely
to be rigorously verifiable and portable to new proof checking systems,
according to the following principles.

* Do not use ```Prop``` or ```Set```, and ensure definitions don't produce
  elements of them.
* Do not use ```Type```, except in ```Foundations/Basics/Preamble.v```.
  Use ```UU``` instead.  If higher universes are needed, they should be
  added to ```Foundations/Basics/Preamble.v```.
* Do not use ```Inductive``` or ```Record```, except in ```Foundations/Basics/Preamble.v```.
* Do not use ```Module``` or ```Structure```.
* Do not use ```Fixpoint```.
* Do not use ```destruct```, ```match```, square brackets with ```intros```, or
  nested square brackets with ```induction```.
* Do not end a proof with ```Qed.```, except with ```Goal```, for that may prevent later computations.
* Start all proofs with ```Proof.``` on a separate line and end it with
  ```Defined.``` on a separate line, as this makes it possible for us to generate
  HTML with expansible/collapsible proofs.

* Use Unicode notation freely, but make the parsing conventions uniform across files, and consider
  putting them into a scope.

Our files don't adhere yet to all of these conventions, but it's a goal we
strive for.

Another advantage of coding in this style is that the proofs should be easier
to transport to another proof assistant.
