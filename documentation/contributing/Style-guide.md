* Avoid inductive types
* Use notation wherever possible (and feasible)
* Make sure that all variables (from induction and intros) are introduced by name
* [Make everything opaque that should be opaque](../guides/Opaqueness)
* Split long definitions into smaller parts. This makes unification faster, allows you to more easily make the right parts opaque and is more readable.
* Structure your proof with [bullets](https://coq.inria.fr/refman/proofs/writing-proofs/proof-mode.html#bullets). An occasional proof part with curly braces is okay, but preferably use bullets. The first three levels are `-`, `+` and `*`. If you need more levels, start with `--` (or maybe `**`), but at that point you should probably start splitting up your proof.
* Minimize your imports: When you create a commit or PR in which you have added `Require Import` statements to a file, or (re)moved code, check that all involved import statements are indeed used or useful. For larger changes, [JasonGross has created a tool](https://github.com/JasonGross/coq-tools) which can come in handy. However, always verify the outcome, because some redundant imports are still good to have (see [this discussion](https://github.com/UniMath/UniMath/issues/1664) for more details).

## Naming
Here is a couple of guidelines for naming different things:
* Names of files, directories and sections should be `CamelCase`.
* Names of definitions and lemmas should be `snake_case`.
* When a file defines a type of object, together with some properties, its name should be plural: `Categories`, `Monoids`, `Limits`. When a file constructs one such thing, it can be singular: `ArrowCategory`.
* Naming (definitions, for example: "x_to_y" or "y_from_x"?)

## Add comments to your code
Keep the following guideline in mind: The top part is what you expect everybody to read. Comments in the middle are harder to find, so you should expect people to read them unless if they go very deeply into the file. Use some inline comments to explain interesting or hard parts of a proof. Regarding the header, it should tell a user what they can find inside the file. Here is a template:
```coq
(**

  Title of one line

  Then a (usually nonoptional) description of what a user should expect in this file,
  useful information about the formalisation and/or references to related research papers.

  Contents
  1. Then a table of contents [the_toc]
  1.1. Explaining the layout of the file [layout]
  2. With the names of the main theorems or definitions in brackets [main_theorem]

 *)
```
Then make sure to refer back to the table of contents with headers inside your code, looking like this (the asterisks are to adhere to [coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html#sections)):
```coq
(** * 1. Then a table of contents *)
...
(** ** 1.1. Explaining the layout of the file *)
```

# Old UniMath coding style. To Be Cleaned Up

In the following rules, we purposely restrict our use of Coq to a subset whose
semantics is more likely to be rigorously verifiable and portable to new proof
checking systems, and we follow a style of coding designed to render proofs
less fragile and to make the files have a more uniform and pleasing appearance.

* Identifiers and function names
  * Form identifiers by concatenating English words or existing identifiers in
    lower case, separating them by underscores.
  * Unless it impedes clarity or goes against common practice avoid using
    abbreviations.
  * In some parts of the library uppercase is used for bundled mathematical
    objects (e.g. `Pullback`, `Topos`).  It is sometimes justified to introduce
    new identifiers using this naming scheme.  The following guidelines should
    then be applied:
    * Identifiers with capital letters must not use underscores to separate
      words, they must use `CamelCase`.
    * Only use `CamelCase` when it is already used in the parts of the library
      you are working in or there is some compelling reason for it to be
      introduced.
    * Do not use `CamelCase` for intermediary structures.  Example: if
      `CamelCase`contains a data part and a property part then name these
      `camel_case_data` and `is_camel_case`, do not call them `CamelCaseData`
      and `IsCamelCase`.
    * Upper-case letters should not be used in function names unless there is
      specific good reason to do so.  In general name your functions
      `make_camel_case` and `camel_case_property`, not `make_CamelCase` and
      `CamelCase_property`, even if the object is called `CamelCase`.
* Do not use `Admitted` or introduce new axioms.
* Do not use `apply` with a term that needs no additional arguments filled in,
  because using `exact` would be clearer.
* Do not use `Prop` or `Set`, and ensure definitions don't produce
  elements of them.
* Do not use `Inductive` or `Record`.  Their use is limited to just a few basic
  types, which are defined in `Foundations/Preamble.v`.
* Do not use `Structure`.
* Use `Module` only naively, to create blocks of code that can be imported.  Do not use `Module Type`.
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
* Avoid ending proofs with `Qed`, because that may prevent future computation. If you decide to make a proof opaque,
  then make sure that its type is a proposition. It is undesirable to write multiple opaque proofs of properties, for then proofs of equality of objects containing them cannot be accomplished by reflexivity.
* Start all proofs with `Proof.` on a separate line and end it with
  `Defined.` on a separate line, as this makes it possible for us to generate
  HTML with expansible/collapsible proofs.
* Use `Lemma`, `Proposition`, or `Theorem` for proofs of propositions;
  for defining elements of types that are not propositions, use
  `Definition`.
* Document the contents of a file with at least a documentation comment at the top of the file.
  This comment explains the scope of the file, as well as its main results.
  It also lists the names of the main definitions and results [in_brackets], which coqdoc recognizes and converts to hyperlinks.
  For more information, [see the wiki](https://github.com/UniMath/UniMath/wiki/Style-Guide#add-comments-to-your-code).
* Use Unicode notation freely, but make the parsing conventions uniform across files.
  All notations, except for certain notations in the Foundations package used everywhere,
  should be local or in a scope.  All scopes, if opened, should be opened only locally.
  Consider also putting them into a submodule, for then they won't be activated even
  for printing.
* When introducing a notation using Unicode characters, document in a comment how to input that character using the Agda input method.
* Each line should be limited to at most 100 (Unicode) characters.  The
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
