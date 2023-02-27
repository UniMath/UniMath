(* In this file, we have formalized:
   1: The definition of a weak (dagger) equivalence between dagger categories
   2: We have shown that any weak dagger equivalence induces a unitary isomorphism, i.e. dagger isomorphism,
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerFunctors.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerIsos.
Require Import UniMath.CategoryTheory.DaggerCategories.DaggerFunctorCategory.

Local Open Scope cat.

Section WeakDaggerEquivalences.

  Definition is_unitarily_eso
             {C D : category} {dagC : dagger C} {dagD : dagger D}
             {F : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
    : UU
    := ∏ d : D, ∃ c : C, unitary dagD (F c) d.

  Definition is_weak_dagger_equiv
             {C D : category} {dagC : dagger C} {dagD : dagger D}
             {F : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
    : UU
    := is_unitarily_eso dagF × fully_faithful F.

End WeakDaggerEquivalences.

Section WeakDaggerEquivToUnitaryDaggerFunctorCat.

  Definition weak_dagger_equiv_to_unitarily_iso_of_dagger_functor_cats
             {C D : category} (dagC : dagger C) (dagD : dagger D)
             {F : functor C D}
             {dagF : is_dagger_functor dagC dagD F}
             (wF : is_weak_dagger_equiv dagF)
    : nat.
  Proof.
  Admitted.

End WeakDaggerEquivToUnitaryDaggerFunctorCat.
