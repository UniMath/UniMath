(** * Groups as universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Open Scope stn.
Open Scope sorted.

Definition group_signature := make_signature_simple_single_sorted [2; 0; 1].

Definition group_mul_op: group_signature := ●0.
Definition group_id_op: group_signature := ●1.
Definition group_inv_op: group_signature := ●2.

Section GroupAlgebra.

  Variable G: gr.

  Definition group_support : shSet (sorts group_signature) := λ _: unit, G.

  Definition group_ops (σ: group_signature)
    : group_support* (arity σ) → group_support (sort σ).
  Proof.
    induction σ as [i ilt].
    induction i as [|i _].
    { exact (λ p, op (pr1 p) (pr12 p)). }
    induction i as [|i _].
    { exact (λ _, unel G). }
    induction i as [|i _].
    { exact (λ p, grinv G (pr1 p)). }
    exact (fromempty (nopathsfalsetotrue ilt)).
  Defined.

  Definition group_algebra : algebra group_signature
    := make_algebra group_support group_ops.

End GroupAlgebra.

(*

Definition group_mul := build_term_curried group_mul_op.
Definition group_id  := build_term_curried group_id_op.
Definition group_inv := build_term_curried group_inv_op.
*)