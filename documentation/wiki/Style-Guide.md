* Avoid inductive types
* Use notation wherever possible (and feasible)
* Make sure that all variables (from induction and intros) are introduced by name
* [Make everything opaque that should be opaque](./On-opaqueness)
* Split long definitions into smaller parts. This makes unification faster, allows you to more easily make the right parts opaque and is more readable.
* Structure your proof with [bullets](https://coq.inria.fr/refman/proofs/writing-proofs/proof-mode.html#bullets). An occasional proof part with curly braces is okay, but preferably use bullets. The first three levels are `-`, `+` and `*`. If you need more levels, start with `--` (or maybe `**`), but at that point you should probably start splitting up your proof.
* Minimize your imports: When you create a commit or PR in which you have added `Require Import` statements to a file, or (re)moved code, check that all involved import statements are indeed used or useful. For larger changes, [JasonGross has created a tool](https://github.com/JasonGross/coq-tools) which can come in handy. However, always verify the outcome, because some redundant imports are still good to have (see [this discussion](https://github.com/UniMath/UniMath/issues/1664) for more details).

(see also [UniMath/README.md](https://github.com/UniMath/UniMath/blob/master/UniMath/README.md))

## Naming
Here is a couple of guidelines for naming different things:
* Names of files, directories and sections should be `CamelCase`.
* Names of definitions and lemmas should be `snake_case`.
* When a file defines a type of object, together with some properties, its name should be plural: `Categories`, `Monoids`, `Limits`. When a file constructs one such thing, it can be singular: `ArrowCategory`.
* Naming (definitions, for example: "x_to_y" or "y_from_x"?)

## Add comments to your code
Keep the following guideline in mind: The top part is what you expect everybody to read. Comments in the middle are harder to find, so you should expect people to read them unless if they go very deeply into the file. Use some inline comments to explain interesting or hard parts of a proof. Regarding the header, it should tell a user what they can find inside the file. Here is a template:
```coq
(**************************************************************************************************

  Title of one line

  Then a (usually nonoptional) description of what a user should expect in this file,
  useful information about the formalisation and/or references to related research papers.

  Contents
  1. Then a table of contents [the_toc]
  1.1. Explaining the layout of the file [layout]
  2. With the names of the main theorems or definitions in brackets [main_theorem]

 **************************************************************************************************)
```
Then make sure to refer back to the table of contents with headers inside your code, looking like this (the asterisks are to adhere to [coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html#sections)):
```coq
(** * 1. Then a table of contents *)
...
(** ** 1.1. Explaining the layout of the file *)
```