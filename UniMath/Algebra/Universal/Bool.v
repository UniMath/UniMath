(***** Universal Algebra: the boolean algebras ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.

Open Scope stn.

Definition bool_signature := mk_signature (vcons 0 (vcons 0 (vcons  1 (vcons 2 vnil)))).

Definition bool_false: names bool_signature := (●0).
Definition bool_true: names bool_signature := (●1).
Definition bool_not: names bool_signature := (●2).
Definition bool_and: names bool_signature := (●3).

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
  { cbn. exact (λ x, negb(pr1 x)). }
  induction n.
  { cbn. exact (λ x, andb (pr1 x) (pr1 (pr2 x))). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition bool_algebra : Algebra bool_signature
  := mk_algebra boolset bool_ops.
