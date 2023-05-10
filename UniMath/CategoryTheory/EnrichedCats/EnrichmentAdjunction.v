(**********************************************************************

 Enriched adjunctions

 In this file, we define the notion of enriched adjunctions. To do so,
 we first define the notion of an enrichment of an adjunction, which
 is a pair of an enrichment for both functors and for the unit and
 counit. An enriched adjunction is a pair of an adjunction together
 with an enrichment.

 Context
 1. Enrichments of adjunctions
 2. Enriched adjunctions

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Enrichments of adjunctions
 *)
Definition adjunction_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (L : adjunction C₁ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (EL : functor_enrichment (left_adjoint L) E₁ E₂)
       (ER : functor_enrichment (right_adjoint L) E₂ E₁),
     (nat_trans_enrichment
        (adjunit L)
        (functor_id_enrichment E₁)
        (functor_comp_enrichment EL ER))
     ×
     (nat_trans_enrichment
        (adjcounit L)
        (functor_comp_enrichment ER EL))
     (functor_id_enrichment E₂).

Definition make_adjunction_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (L : adjunction C₁ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (EL : functor_enrichment (left_adjoint L) E₁ E₂)
           (ER : functor_enrichment (right_adjoint L) E₂ E₁)
           (Eη : nat_trans_enrichment
                   (adjunit L)
                   (functor_id_enrichment E₁)
                   (functor_comp_enrichment EL ER))
           (Eε : nat_trans_enrichment
                   (adjcounit L)
                   (functor_comp_enrichment ER EL)
                   (functor_id_enrichment E₂))
  : adjunction_enrichment L E₁ E₂
  := EL ,, ER ,, Eη ,, Eε.

Section Accessors.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {L : adjunction C₁ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (EL : adjunction_enrichment L E₁ E₂).

  Definition left_adjoint_enrichment
    : functor_enrichment (left_adjoint L) E₁ E₂
    := pr1 EL.

  Definition right_adjoint_enrichment
    : functor_enrichment (right_adjoint L) E₂ E₁
    := pr12 EL.

  Definition adjoint_unit_enrichment
    : nat_trans_enrichment
        (adjunit L)
        (functor_id_enrichment E₁)
        (functor_comp_enrichment
           left_adjoint_enrichment
           right_adjoint_enrichment)
    := pr122 EL.

  Definition adjoint_counit_enrichment
    : nat_trans_enrichment
        (adjcounit L)
        (functor_comp_enrichment
           right_adjoint_enrichment
           left_adjoint_enrichment)
        (functor_id_enrichment E₂)
    := pr222 EL.
End Accessors.

(**
 2. Enriched adjunctions
 *)
Definition enriched_adjunction
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (L : adjunction C₁ C₂), adjunction_enrichment L E₁ E₂.

Coercion enriched_adjunction_to_adjunction
         {V : monoidal_cat}
         {C₁ C₂ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         (L : enriched_adjunction E₁ E₂)
  : adjunction C₁ C₂
  := pr1 L.

Coercion enriched_adjunction_to_enrichment
         {V : monoidal_cat}
         {C₁ C₂ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         (L : enriched_adjunction E₁ E₂)
  : adjunction_enrichment L E₁ E₂
  := pr2 L.
