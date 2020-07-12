(** * Boolean signature and the standard boolean algebra *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Open Scope stn.
Open Scope sorted.

Definition bool_signature := make_signature_simple_single_sorted [0; 0; 1; 2; 2 ].

Definition bool_false_op : bool_signature := ●0.
Definition bool_true_op : bool_signature := ●1.
Definition bool_not_op : bool_signature := ●2.
Definition bool_and_op : bool_signature := ●3.
Definition bool_or_op : bool_signature := ●4.

Definition bool_support: shSet (sorts bool_signature) := λ _, boolset.

Definition bool_ops (σ: bool_signature): bool_support* (arity σ) → bool_support (sort σ).
Proof.
  induction σ as [n proofn].
  induction n.
  { cbn. exact (λ _, false). }
  induction n.
  { cbn. exact (λ _, true). }
  induction n.
  { cbn. exact (λ x, negb (pr1 x)). }
  induction n.
  { cbn. exact (λ x, andb (pr1 x) (pr12 x)). }
  induction n.
  { cbn. exact (λ x, orb (pr1 x) (pr12 x)). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition bool_algebra : algebra bool_signature
  := make_algebra bool_support bool_ops.

(*

Definition bool_false := build_term_curried bool_false_op.
Definition bool_true := build_term_curried bool_true_op.
Definition bool_not := build_term_curried bool_not_op.
Definition bool_and := build_term_curried bool_and_op.
Definition bool_or := build_term_curried bool_or_op.

*)