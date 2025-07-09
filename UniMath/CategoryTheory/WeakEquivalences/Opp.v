(**
   Opposite Of Weak Equivalences

   In this file, we show that the opposite of a weak equivalence is a weak equivalence.

   Contents.
   1. Opposite of a weak equivalence [opp_is_weak_equiv]
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

(** * 1. Opposite Of Weak Equivalence *)
Lemma opp_is_weak_equiv
  {C D : category} {F : functor C D} (F_weq : is_weak_equiv F)
  : is_weak_equiv (functor_op F).
Proof.
  split.
  - apply opp_functor_essentially_surjective.
    exact (pr1 F_weq).
  - apply opp_functor_fully_faithful.
    exact (pr2 F_weq).
Qed.
