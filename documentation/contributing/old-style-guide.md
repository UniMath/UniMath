## UniMath coding style

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
