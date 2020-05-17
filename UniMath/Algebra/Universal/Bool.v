(** * Boolean signature and the standard boolean algebra *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.

Open Scope stn.

Definition bool_signature :=
  make_signature_simple
    (vcons 0                                        (* false *)
           (vcons 0                                 (* true *)
                  (vcons 1                          (* not *)
                         (vcons 2                   (* and *)
                                (vcons 2            (* or *)
                                       vnil))))).

Definition bool_false_op: names bool_signature := ●0.
Definition bool_true_op: names bool_signature := ●1.
Definition bool_not_op: names bool_signature := ●2.
Definition bool_and_op: names bool_signature := ●3.
Definition bool_or_op: names bool_signature := ●4.

Local Definition andb (b1 b2: bool): bool := if b1 then b2 else false.
Local Definition orb (b1 b2: bool): bool := if b1 then true else b2.

Definition bool_ops (nm : names bool_signature): Vector bool (arity nm) → bool.
Proof.
  induction nm as [n proofn].
  induction n.
  { cbn. exact (λ _, false). }
  induction n.
  { cbn. exact (λ _, true). }
  induction n.
  { cbn. exact (λ x, negb (pr1 x)). }
  induction n.
  { cbn. exact (λ x, andb (pr1 x) (pr1 (pr2 x))). }
  induction n.
  { cbn. exact (λ x, orb (pr1 x) (pr1 (pr2 x))). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition bool_algebra : algebra bool_signature
  := make_algebra boolset bool_ops.

Definition bool_false := build_term_curried bool_false_op.
Definition bool_true := build_term_curried bool_true_op.
Definition bool_not := build_term_curried bool_not_op.
Definition bool_and := build_term_curried bool_and_op.
Definition bool_or := build_term_curried bool_or_op.
