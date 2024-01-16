(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011

This is the first in the group of files which contain the (current state of) the mathematical
library for the proof assistant Coq based on the Univalent Foundations.  It contains some new
notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)

(** Initial setup unrelated to Univalent Foundations *)

Require Export UniMath.Foundations.Init.

(** Universe structure *)

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

(** The empty type *)

Inductive empty : UU := .

Notation "∅" := empty.

(** The one-element type *)

Inductive unit : UU :=
    tt : unit.

(** The two-element type *)

Inductive bool : UU :=
  | true : bool
  | false : bool.

Definition negb (b:bool) := if b then false else true.

(** The coproduct of two types *)

Inductive coprod (A B:UU) : UU :=
| ii1 : A -> coprod A B
| ii2 : B -> coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation inl := ii1.            (* deprecated; will be removed eventually *)
Notation inr := ii2.            (* deprecated; will be removed eventually *)

Notation "X ⨿ Y" := (coprod X Y).
(* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)

(** The natural numbers *)

(* Declare ML Module "nat_syntax_plugin".


In the context of Coq, we can represent the structure of the universe using a type UU. We use coercion to convert this type to Sortclass, which allows us to define different types such as the empty type, one-element type, and coproduct of two types. The negation function is also defined for the boolean type. The coproduct is represented by the inl and inr notations, which will eventually be replaced with a more concise syntax using the "X ⨿ Y" notation. Finally, we define the natural numbers using the ML module "nat\_syntax\_plugin".


 *)

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Definition succ := S.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.

(* note: our mul differs from that in Coq.Init.Nat  *)
Definition mul : nat -> nat -> nat.
Proof.
  intros n m.
  induction n as [|p pm].
  - exact O.
  - exact (pm + m).
Defined.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint max n m :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m :=
  match n, m with
    | O, _ => O
    | S n', O => O
    | S n', S m' => S (min n' m')
  end.

Notation  "0" := (O) : nat_scope.
Notation  "1" := (S 0) : nat_scope.
Notation  "2" := (S 1) : nat_scope.
Notation  "3" := (S 2) : nat_scope.
Notation  "4" := (S 3) : nat_scope.
Notation  "5" := (S 4) : nat_scope.
Notation  "6" := (S 5) : nat_scope.
Notation  "7" := (S 6) : nat_scope.
Notation  "8" := (S 7) : nat_scope.
Notation  "9" := (S 8) : nat_scope.
Notation "10" := (S 9) : nat_scope.
Notation "11" := (S 10) : nat_scope.
Notation "12" := (S 11) : nat_scope.
Notation "13" := (S 12) : nat_scope.
Notation "14" := (S 13) : nat_scope.
Notation "15" := (S 14) : nat_scope.
Notation "16" := (S 15) : nat_scope.
Notation "17" := (S 16) : nat_scope.
Notation "18" := (S 17) : nat_scope.
Notation "19" := (S 18) : nat_scope.
Notation "20" := (S 19) : nat_scope.
Notation "21" := (S 20) : nat_scope.
Notation "22" := (S 21) : nat_scope.
Notation "23" := (S 22) : nat_scope.
Notation "24" := (S 23) : nat_scope.
Notation "100" := (10 * 10) : nat_scope.
Notation "1000" := (10 * 100) : nat_scope.

(** Identity Types

**"Identity Paths and Their Types"**

Inductive types have been a subject of interest in the field of programming languages, specifically in Coq, a formal verification system. Within Coq, identity types refer to a type that indicates whether two values are equal or not. In this code snippet, we define two functions: `paths_refl` and `idpath`.

`paths_refl` is an inductive function that takes an element `a` from the type `A` and returns a value of type `UU`, which stands for "universe of universes." This function is responsible for returning a reference loop, which can be used to create an identity path.

The `idpath` notation is shorthand for `paths_refl`. It represents the creation of an identity path between two values, and we use it extensively throughout our code.

By defining these functions and notations, we can work with identity types in a more concise and efficient manner within Coq. This makes it easier to reason about the properties of our programs and ensure that they are correct.

 *)

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
#[global]
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .

(* Remark: all of the uu0.v now uses only paths_rect and not the direct "match" construction
on paths. By adding a constantin paths for the computation rule for paths_rect and then making
both this constant and paths_rect itself opaque it is possible to check which of the
constructions of the uu0 can be done with the weakened version of the Martin-Lof Type Theory
that is interpreted by the Bezem-Coquand-Huber cubical set model of 2014. *)

(** Dependent sums.

One can not use a new record each time one needs it because the general theorems about this
construction would not apply to new instances of "Record" due to the "generativity" of inductive
definitions in Coq.

We use "Record", which is equivalent to "Structure", instead of "Inductive" here, so we can take
advantage of the "primitive projections" feature of Coq, which introduces η-reduction for pairs, by
adding the option "Set Primitive Projections".  It also speeds up compilation by 56 percent.

The terms produced by the "induction" tactic, when we define "total2" as a record, contain the
"match" construction instead appealing to the eliminator.  However, assuming the eliminator will be
justified mathematically, the way to justify the the "match" construction is to point out that it
can be regarded as an abbreviation for the eliminator that omits explicit mention of the first two
parameters (X:Type) and (Y:X->Type).

I.e., whenever you see

       [match w as t0 return TYPE with | tpair _ _ x y => BODY end]

in a proof term, just mentally replace it by

       [@total2_rect _ _ (λ t0, TYPE) (λ x y, BODY) w]

*)

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.
  (* total2 *)
  (*      : (?T → UU) → Type *)
  (* where *)
(* ?T : [ |- UU]
#+begin_src output

We can represent the total2 function as a tuple of two functions: pr1 and pr2, with the type parameter T. The type of pr1 is T, while the type of pr2 is P(T). Both pr1 and pr2 are expected to be functions that take in an input of type T and output an object of type UU.

To use this function, we can create a tuple with two parameters: pr1 and pr2. This tuple represents the total2 function, which takes in two functions (of types T and P(T)) and outputs a tuple containing both functions.

This reinterpretation preserves the main ideas of the original code while using a more creative approach to represent the function.
#+end_src

 *)

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Notation "x ,, y" := (tpair _ x y).
