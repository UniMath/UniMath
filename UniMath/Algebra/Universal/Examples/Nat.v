(** * Example on natural numbers *)

(**
  This file contains the definition of the signature of natural numbers, the standard algebra,
  the boolean algebra and the morphism between them.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope stn.
Local Open Scope hom.

Definition nat_signature := make_signature_simple_single_sorted [ 0 ; 1 ].

Definition nat_sort: sorts nat_signature := tt.

Definition nat_zero_op: names nat_signature := ●0.
Definition nat_succ_op: names nat_signature := ●1.

Definition nat_algebra := make_algebra_simple_single_sorted nat_signature natset [( λ _, 0 ;  λ x, S (pr1 x) )].

Goal nat_algebra nat_zero_op tt = 0.
Proof. apply idpath. Defined.

Goal nat_algebra nat_succ_op (1 ,, tt) = 2.
Proof. apply idpath. Defined.

Definition z2_algebra := make_algebra_simple_single_sorted nat_signature boolset [( λ _, false ; λ x, negb (pr1 x) )].

Definition nat_to_z2 : nat_algebra s→ z2_algebra
  := λ s: sorts nat_signature, nat_rect (λ _, bool) false (λ n HP, negb HP).
  
Goal nat_to_z2 nat_sort 0 = false.
Proof. apply idpath. Defined.

Goal nat_to_z2 nat_sort 1 = true.
Proof. apply idpath. Defined.

Goal nat_to_z2 nat_sort 2 = false.
Proof. apply idpath. Defined.

Lemma ishom_nat_to_z2: @ishom _ nat_algebra z2_algebra (nat_to_z2).
Proof.
  unfold ishom.
  intros.
  induction nm as [n proofn].
  inductive_reflexivity n proofn.
Defined.

Definition natz2 : nat_algebra ↦ z2_algebra := make_hom ishom_nat_to_z2.

Definition nat_zero := build_term_curried nat_zero_op.
Definition nat_succ := build_term_curried nat_succ_op.

Definition nat2term (n: nat): term nat_signature nat_sort
  := nat_rect
       (λ _, term nat_signature nat_sort)
       nat_zero
       (λ (n: nat) (tn: term nat_signature nat_sort), nat_succ tn)
       n.
