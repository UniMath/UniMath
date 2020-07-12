(** * Lists as universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Open Scope stn.
Open Scope sorted.

Definition data_sort: ⟦ 2 ⟧ := ●0.
Definition list_sort: ⟦ 2 ⟧ := ●1.

Definition list_signature: signature
  := make_signature_simple 2 [ (nil ,, list_sort) ;  ( [data_sort ; list_sort] ,, list_sort ) ].

Definition nil_op: list_signature := ●0.
Definition cons_op: list_signature := ●1.

Section ListAlgebra.

  Variable A: hSet.

  Definition list_support : shSet (sorts list_signature):= nth [ A ; listset A ].

  Definition list_ops (σ: list_signature)
    : list_support* (arity σ) → list_support (sort σ).
  Proof.
    induction σ as [i ilt].
    induction i as [|i _].
    { exact (λ _, nil). }
    induction i as [|i _].
    { exact (λ p, cons (pr1 p) (pr12 p)). }
    exact (fromempty (nopathsfalsetotrue ilt)).
  Defined.

End ListAlgebra.

