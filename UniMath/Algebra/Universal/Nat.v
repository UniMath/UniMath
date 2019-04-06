(***** Universal Algebra: the natural number algebras ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.

Open Scope stn.

Definition nat_signature: Signature := make_signature_from_vector (vcons 0 (vcons 1 vnil)).

Definition nat_zero: names nat_signature := (●0).
Definition nat_succ: names nat_signature := (●1).

Definition nat_algebra: Algebra nat_signature.
  red.
  exists natset.
  intro.
  cbn in nm.
  destruct nm as [n proofn].
  induction n.
  { cbn. exact (λ _, 0). }
  induction n.
  { cbn. exact (λ x, S(pr1 x)). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.
