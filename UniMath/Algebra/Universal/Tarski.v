(** * Semantics for boolean formulas. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Bool.
Require Import UniMath.Algebra.Universal.Equations.
Require Import UniMath.Algebra.Universal.Bool.

Open Scope stn.

Definition σ := vsignature bool_signature.
Definition T := vterm bool_signature.

Definition bool_false_op: names σ := inl (●0).
Definition bool_true_op : names σ := inl (●1).
Definition bool_not_op  : names σ := inl (●2).
Definition bool_and_op  : names σ := inl (●3).
Definition bool_or_op   : names σ := inl (●4).

Definition bool_false := build_term_curried bool_false_op.
Definition bool_true  := build_term_curried bool_true_op.
Definition bool_not   := build_term_curried bool_not_op.
Definition bool_and   := build_term_curried bool_and_op.
Definition bool_or    := build_term_curried bool_or_op.

Definition interp (v:nat->bool) (x:T) : bool
  := fromvterm (op bool_algebra) v x.

(** ** Examples. *)

Definition x : T := var 0.
Definition y : T := var 1.
Definition z : T := var 2.

Definition f (n : nat) : bool.
Proof.
  induction n as [|n Hn].
  - exact true.
  - exact false.
Defined.

(** ** Tests. *)
Eval lazy in interp f (bool_and x bool_true).
Eval lazy in interp f (bool_and x y).
Eval lazy in interp f (bool_or x y).
Eval lazy in interp f (bool_or x (bool_and y bool_false)).
