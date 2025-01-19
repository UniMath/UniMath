(**********************************************************************

 The empty enriched category

 In this file, we define the empty enriched categories, which is the
 enriched categories without any objects. In addition, we provide the
 necessary functors and natural transformations in order to prove that
 it is a strict biinitial object in the bicategory of enriched
 categories.

 Contents
 1. The empty enriched category
 2. Functors from the empty enriched category
 3. Natural transformations involving the empty enriched category

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedEmpty.
  Context (V : monoidal_cat).

  (**
   1. The empty enriched category
   *)
  Definition empty_category_enrichment_data
    : enrichment_data empty_category V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x, fromempty x).
    - exact (λ x, fromempty x).
    - exact (λ x, fromempty x).
    - exact (λ x, fromempty x).
    - exact (λ x, fromempty x).
  Defined.

  Definition empty_category_enrichment
    : enrichment empty_category V.
  Proof.
    simple refine (_ ,, _).
    - exact empty_category_enrichment_data.
    - abstract
        (repeat split ; intro x ; induction x).
  Defined.

  (**
   2. Functors from the empty enriched category
   *)
  Definition functor_from_empty_enrichment
             {C : category}
             (E : enrichment C V)
    : functor_enrichment
        (functor_from_empty C)
        empty_category_enrichment
        E.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (λ x, fromempty x).
    - abstract
        (intro x ; induction x).
    - abstract
        (intro x ; induction x).
    - abstract
        (intro x ; induction x).
  Defined.

  (**
   3. Natural transformations involving the empty enriched category
   *)
  Definition nat_trans_from_empty_enrichment
             {C : category}
             {E : enrichment C V}
             {F G : empty_category ⟶ C}
             (FE : functor_enrichment F empty_category_enrichment E)
             (GE : functor_enrichment G empty_category_enrichment E)
    : nat_trans_enrichment
        (nat_trans_from_empty F G)
        FE
        GE.
  Proof.
    intro x.
    induction x.
  Qed.

  Definition nat_trans_to_empty_enrichment
             {C₁ C₂ : category}
             {E₁ : enrichment C₁ V}
             {E₂ : enrichment C₂ V}
             {F : C₁ ⟶ empty_category}
             (EF : functor_enrichment F E₁ empty_category_enrichment)
             {G : empty_category ⟶ C₂}
             (EG : functor_enrichment G empty_category_enrichment E₂)
             {H : C₁ ⟶ C₂}
             (EH : functor_enrichment H E₁ E₂)
    : nat_trans_enrichment
        (nat_trans_to_empty F G H)
        EH
        (functor_comp_enrichment EF EG).
  Proof.
    intros x.
    induction (F x).
  Qed.

  Definition nat_trans_to_empty_inv_enrichment
             {C₁ C₂ : category}
             {E₁ : enrichment C₁ V}
             {E₂ : enrichment C₂ V}
             {F : C₁ ⟶ empty_category}
             (EF : functor_enrichment F E₁ empty_category_enrichment)
             {G : empty_category ⟶ C₂}
             (EG : functor_enrichment G empty_category_enrichment E₂)
             {H : C₁ ⟶ C₂}
             (EH : functor_enrichment H E₁ E₂)
    : nat_trans_enrichment
        (nat_z_iso_inv
           (make_nat_z_iso _ _ _ (nat_trans_to_empty_is_nat_z_iso F G H)))
        (functor_comp_enrichment EF EG)
        EH.
  Proof.
    intros x.
    induction (F x).
  Qed.
End EnrichedEmpty.
