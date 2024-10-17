Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section EmptySieve.

  Context {C : category}.
  Context (X : C).

  Definition empty_sieve_functor
    : PreShv C
    := InitialObject Initial_PreShv.

  Definition empty_sieve_nat_trans
    : (empty_sieve_functor : _ ⟶ _) ⟹ (yoneda C X : _ ⟶ _)
    := InitialArrow Initial_PreShv _.

  Lemma empty_sieve_is_monic
    : isMonic (C := PreShv C) empty_sieve_nat_trans.
  Proof.
    apply is_nat_trans_monic_from_pointwise_monics.
    intro a.
    apply (invmap (MonosAreInjective_HSET _)).
    intro e.
    induction e.
  Qed.

  Definition empty_sieve
    : Sieves.sieve X
    := (empty_sieve_functor ,, tt) ,,
      make_Monic (PreShv C) empty_sieve_nat_trans empty_sieve_is_monic.

End EmptySieve.
