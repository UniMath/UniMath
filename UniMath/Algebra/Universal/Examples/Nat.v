(** * Natural numbers signature and the standard algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Open Scope stn.
Open Scope sorted.
Open Scope hom.

Definition nat_signature := make_signature_simple_single_sorted [ 0; 1 ].

Definition nat_zero_op: nat_signature := ●0.
Definition nat_succ_op: nat_signature := ●1.

Definition nat_support: shSet (sorts nat_signature) := λ _, natset.

Definition nat_ops (σ : nat_signature): nat_support* (arity σ) → nat_support (sort σ).
Proof.
  induction σ as [n proofn].
  induction n.
  { cbn. exact (λ _, 0). }
  induction n.
  { cbn. exact (λ x, S(pr1 x)). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition nat_algebra: algebra nat_signature
  := make_algebra nat_support nat_ops.

Goal nat_algebra nat_zero_op tt = 0.
Proof. apply idpath. Defined.

Goal nat_algebra nat_succ_op (1 ,, tt) = 2.
Proof. apply idpath. Defined.

Definition z2_support: shSet (sorts nat_signature) := λ _, boolset.

Definition z2_ops (σ : nat_signature): z2_support* (arity σ) → z2_support (sort σ).
Proof.
  induction σ as [n proofn].
  induction n.
  { cbn. exact (λ _, false). }
  induction n.
  { cbn. exact (λ x, negb (pr1 x)). }
  { exact (fromempty (nopathsfalsetotrue proofn)). }
Defined.

Definition z2_algebra: algebra nat_signature
  := make_algebra z2_support z2_ops.

Definition nat_to_z2 : nat_support s→ z2_support
  := λ s: sorts nat_signature, nat_rect (λ _, bool) false (λ n HP, negb HP).

Goal nat_to_z2 tt 0 = false.
Proof. apply idpath. Defined.

Goal nat_to_z2 tt 1 = true.
Proof. apply idpath. Defined.

Goal nat_to_z2 tt 2 = false.
Proof. apply idpath. Defined.

Lemma ishom_nat_to_z2: @ishom _ nat_algebra z2_algebra (nat_to_z2).
Proof.
  unfold ishom.
  intros.
  induction σ as [n proofn].
  inductive_reflexivity n proofn.
Defined.

Definition natz2 : nat_algebra ↦ z2_algebra := make_hom ishom_nat_to_z2.

(*

Definition nat_zero := build_term_curried nat_zero_op.
Definition nat_succ := build_term_curried nat_succ_op.

Definition nat2term (n: nat): term nat_signature
  := nat_rect
       (λ _, term nat_signature)
       nat_zero
       (λ (n: nat) (tn: term nat_signature), nat_succ tn)
       n.
*)