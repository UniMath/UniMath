(*************************************************************************

 The Rezk Completion for Enriched Categories

 We use the Yoneda lemma and the image factorization to construct the
 Rezk completion for enriched categories. For this construction, we have
 to assume that the monoidal category `V` over which we enrich, is a
 univalent category. The structure of the proof is the mostly same as for
 ordinary categories. The main difference is that instead of looking at
 all presheaves, we only look at those presheaves that are enriched.

 Contents
 1. The Rezk completion and its enrichment
 2. The weak equivalence

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.ImageEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Yoneda.
Require Import UniMath.CategoryTheory.EnrichedCats.YonedaLemma.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedRezkCompletion.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (EqV : Equalizers V)
          (PV : Products C V)
          (PV' : Products (C × C) V)
          (HV : is_univalent V).

  (** * 1. The Rezk completion and its enrichment *)
  Definition enriched_rezk_completion
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact (full_img_sub_precategory (enriched_yoneda_functor E)).
    - use is_univalent_full_sub_category.
      use is_univalent_enriched_functor_cat.
      exact HV.
  Defined.

  Definition enriched_rezk_completion_enrichment
    : enrichment enriched_rezk_completion V.
  Proof.
    use image_enrichment.
    exact (enriched_presheaf_enrichment E EqV PV PV').
  Defined.

  (** * 2. The weak equivalence *)
  Definition enriched_rezk_completion_map
    : C ⟶ enriched_rezk_completion
    := functor_full_img _.

  Definition enriched_rezk_completion_map_enrichment
    : functor_enrichment
        enriched_rezk_completion_map
        E
        enriched_rezk_completion_enrichment.
  Proof.
    apply image_proj_enrichment.
    apply enriched_yoneda_enrichment.
  Defined.

  Proposition is_essentially_surjective_enriched_rezk_completion_map
    : essentially_surjective enriched_rezk_completion_map.
  Proof.
    apply functor_full_img_essentially_surjective.
  Qed.

  Proposition is_fully_faithful_enriched_rezk_completion_map
    : fully_faithful_enriched_functor enriched_rezk_completion_map_enrichment.
  Proof.
    exact (fully_faithful_enriched_factorization_precomp
             (enriched_yoneda_enrichment E EqV PV PV')
             enriched_rezk_completion_map_enrichment
             _
             (image_factorization_enriched_commutes_inv _)
             (fully_faithful_enriched_yoneda _ _ _ _)
             image_incl_enrichment_fully_faithful).
  Qed.
End EnrichedRezkCompletion.
