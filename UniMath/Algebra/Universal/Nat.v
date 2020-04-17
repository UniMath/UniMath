(***** Universal Algebra: the natural numbers signature and standard algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.

Open Scope stn.

Definition nat_signature: signature
  := make_signature_simple
       (vcons 0             (* zero *)
         (vcons 1 vnil)).   (* succ *)

Definition nat_zero_op: names nat_signature := ●0.
Definition nat_succ_op: names nat_signature := ●1.

Definition nat_ops (nm : names nat_signature): Vector nat (arity nm) → nat.
Proof.
  induction nm as [n proofn].
  induction n.
  { cbn. exact (λ _, 0). }
  induction n.
  { cbn. exact (λ x, S(pr1 x)). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition nat_algebra : algebra nat_signature
  := make_algebra natset nat_ops.

Definition nat_zero := build_term_curried nat_zero_op.
Definition nat_succ := build_term_curried nat_succ_op.

Definition nat2term (n: nat): term nat_signature
  := nat_rect
       (λ _, term nat_signature)
       nat_zero
       (λ (n: nat) (tn: term nat_signature), nat_succ tn)
       n.
