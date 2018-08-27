Univalent Mathematics Coq files
===============================

Each subdirectory of this directory consists of a separate package, with
various authors, as recorded in the README (or README.md) file in it.

## Contributing code to UniMath

Volunteers may look at unassigned issues at github and volunteer to be assigned
one of them.  New proposals and ideas may be submitted as issues at github for
discussion and feedback.

Contributions are submitted in the form of pull requests at github and are
subject to approval by the UniMath Development Team.

Changes to the package "Foundations" are normally not accepted, for we are
trying to keep it in a state close to what Vladimir Voevodsky originally
intended.  A warning is issued if you run `make` or `make all` and have changed
a file in the Foundations package.

## Adding a file to a package

Each package contains a subdirectory called ".package".  The file
".packages/files" consists of a list of the paths to the *.v files of the
package, in order, i.e., a file is listed after files it depends on.
(That's just so the TAGS file will be correctly sequenced.)  To add a file to a
package, add its path to that file.

## Adding a new package

Create a subdirectory of this directory, populate it with your files, add a
README (or README.md) file, and add a file .package/files, listing the *.v
files of your package, as above.  Then add the name of your package to the head
of the list assigned to "PACKAGES" in the file "./Makefile", or, alternatively,
if you'd like to test your package without modifying "./Makefile", which you might
accidentally commit and push, add its name to the head of the list in
"../build/Makefile-configuration", which is created from
"../build/Makefile-configuration-template".

## The UniMath formal language

The formal language used in the UniMath project is based on Martin-Löf type
theory, as present in MLTT79 below.  We are currently on version 2.

UniMath-1 is MLTT79 except:

- the bound variable in a λ-expression is annotated with its type
- we omit W-types
- just the finite types of cardinality 0, 1, and 2 are used, although there would be no problem with introducing further ones
- we omit reflection from identities to judgmental equalities
- we add the resizing rules from the [slides](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf) of Voevodsky's 2011 talk in Bergen

UniMath-2 is UniMath-1 except:

- we add η for pairs

The axioms accepted are: the univalence axiom, the law of excluded middle, the
axiom of choice, and a few new variants of the axiom of choice, validated by
the semantic model.

MLTT79 is this paper:
```
@incollection {MLTT79,
    AUTHOR = {Martin-L\"of, Per},
     TITLE = {Constructive mathematics and computer programming},
 BOOKTITLE = {Logic, methodology and philosophy of science, {VI} ({H}annover, 1979)},
    SERIES = {Stud. Logic Found. Math.},
    VOLUME = {104},
     PAGES = {153--175},
 PUBLISHER = {North-Holland, Amsterdam},
      YEAR = {1982},
   MRCLASS = {03F50 (03B70 03F55 68Q45)},
  MRNUMBER = {682410},
MRREVIEWER = {B. H. Mayoh},
       DOI = {10.1016/S0049-237X(09)70189-2},
       URL = {http://dx.doi.org/10.1016/S0049-237X(09)70189-2},
}
```

## UniMath coding style

In the following rules, we purposely restrict our use of Coq to a subset whose
semantics is more likely to be rigorously verifiable and portable to new proof
checking systems, and we follow a style of coding designed to render proofs
less fragile and to make the files have a more uniform and pleasing appearance.

* Do not use `Admitted` or introduce new axioms.
* Do not use `apply` with a term that needs no additional arguments filled in,
  because using `exact` would be clearer.
* Do not use `Prop` or `Set`, and ensure definitions don't produce
  elements of them.
* Do not use `Inductive` or `Record`.  Their use is limited to just a few basic
  types, which are defined in `Foundations/Preamble.v`.
* Do not use `Module` or `Structure`.
* Do not use `Fixpoint`.
* Do not use `destruct`, `match`, `case`, square brackets with `intros`, or
  nested square brackets with `induction`.  (The goal is to prevent generation of
  proof terms using `match`.)
* Use `do` with a specific numerical count, rather than `repeat`, to make proofs
  easier to repair.
* Use `as` to name all new variables introduced by `induction` or
  `destruct`, if the corresponding type is defined in a remote location,
  because different names might be used by Coq when the definition of the type
  is changed.  Name all variables introduced by `assert`, if they are used by
  name later, with `as` or to the left of a colon.
* Do not end a proof with `Qed.`, except with `Goal`, for that may prevent later computations.
* Start all proofs with `Proof.` on a separate line and end it with
  `Defined.` on a separate line, as this makes it possible for us to generate
  HTML with expansible/collapsible proofs.
* Use `Lemma`, `Proposition`, or `Theorem` for proofs of propositions;
  for defining elements of types that are not propositions, use
  `Definition`.
* Use Unicode notation freely, but make the parsing conventions uniform across files, and consider
  putting them into a scope.
* Each line should be limited to at most 100 (unicode) characters.  The
  makefile target `enforce-max-line-length` can be used to detect nonconforming
  files, and the target `show-long-lines` can be used to display the
  nonconforming lines.
* Always use Coq's proof structuring syntax ( ` { } + - * ` ) to focus on a
  single goal immediately after a tactic creates additional goals.
* Indentation should normally be that produced automatically by emacs' `coq-mode`.
* When using `abstract` in a proof, it is unsound to refer later by name to the
  abstracted lemma (whose name typically ends with `_subproof`), because
  its type may vary from one version of Coq to another.  Coq's current behavior is also
  unlikely to be duplicated precisely by a future proof assistant. 
* Define and use accessor functions for structures instead of chains
  of `pr1` and `pr2`. This makes the code easier to maintain in the
  long run (if the structure is rearranged the proofs will still work
  if the accessor functions are changed accordingly).
* Define constructor functions for structures taking all of the
  required data in the right order. This way one can write `use
  constructor` instead of having a nested chain of `use tpair` leading
  to flatter proof scripts for instantiating structures.

Our files don't adhere yet to all of these conventions, but it's a goal we
strive for.

Another advantage of coding in this style is that the proofs should be easier
to transport to another proof assistant.
