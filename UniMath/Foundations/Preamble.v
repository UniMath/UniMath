(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011

This is the first in the group of files which contain the (current state of) the mathematical
library for the proof assistant Coq based on the Univalent Foundations.  It contains some new
notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)

(** Initial setup unrelated to Univalent Foundations *)

Require Export UniMath.Foundations.Init.

(** Universe structure *)

Monomorphic Universe uu0.       (* level 0 -- resized propositions and elements of hProp live here *)
Monomorphic Universe uu1.       (* level 1 -- empty, unit, bool, nat, and hProp live here *)
Monomorphic Universe uu2.       (* level 2 -- hPropset, unitset, natset, ... live here *)

Constraint uu0 < uu1, uu1 < uu2.

Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.
Global Unset Universe Minimization ToSet.

Notation UU  := Type (only parsing).
Notation UU0 := Type@{uu0} (only parsing).
Notation UU1 := Type@{uu1} (only parsing). (* else we get this: Notation UU1 := UU2 *)
Notation UU2 := Type@{uu2} (only parsing).

(* for debugging, temporarily: *)
Global Set Printing Universes.
Global Set Printing Coercions.
Global Unset Printing Notations.

(** The empty type *)

Monomorphic Inductive empty : UU1 := .

Notation "∅" := empty.

(** The one-element type *)

Monomorphic Inductive unit : UU1 :=
  | tt : unit.

(** The two-element type *)

Monomorphic Inductive bool : UU1 :=
  | true : bool
  | false : bool.

Definition negb (b:bool) := if b then false else true.

(** The coproduct of two types *)

Monomorphic Inductive coprod (A B:UU) : UU :=
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

(* Declare ML Module "nat_syntax_plugin". *)

Monomorphic Inductive nat : UU1 :=
  | O : nat
  | S : nat -> nat.

Definition succ := S.

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

(** Identity Types *)

Inductive paths@{i} {A:Type@{i}} (a:A) : A -> Type@{i} := idpath : paths a a.
Hint Resolve idpath : core .
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.

(* Remark: in general we strive to use only paths_rect and not the direct "match" construction on
paths. By adding a constant in paths for the computation rule for paths_rect and then making both
this constant and paths_rect itself opaque it is possible to check which of the constructions of the
uu0 can be done with the weakened version of the Martin-Lof Type Theory that is interpreted by the
Bezem-Coquand-Huber cubical set model of 2014. *)

(** Dependent sums.

One can not use a new record each time one needs it because the general theorems about this
construction would not apply to new instances of "Record" due to the "generativity" of inductive
definitions in Coq.

We use "Record", which is equivalent to "Structure", instead of "Inductive" here, so we can take
advantage of the "primitive projections" feature of Coq, which introduces η-reduction for pairs, by
adding the option "Set Primitive Projections".  It also speeds up compilation by 56 percent.

*)

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Record total2@{i} {T : Type@{i}} (P : T -> Type@{i}) : Type@{i}
  := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Notation "x ,, y" := (tpair _ x y).
