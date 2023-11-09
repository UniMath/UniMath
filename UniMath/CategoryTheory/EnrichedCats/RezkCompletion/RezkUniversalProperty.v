(********************************************************************************

 The universal property of the enriched Rezk completion

 To prove the universal property of the Rezk completion of enriched categories,
 we need to prove that precomposition with a weak equivalence gives rise to an
 adjoint equivalence between functor categories to univalent categories. To prove
 this statement, we show that this precomposition functor is both fully faithful
 and essentially surjective. This file contains the statement that precomposition
 with a fully faithful and essential surjective enriched functor is an adjoint
 equivalence ([enriched_rezk_completion_ump]).

 Contents
 1. Universal property of the Rezk completion
 2. Accessors for the universal property of the Rezk completion

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Precomposition.
Require Export UniMath.CategoryTheory.EnrichedCats.RezkCompletion.PrecompFullyFaithful.
Require Export UniMath.CategoryTheory.EnrichedCats.RezkCompletion.PrecompEssentiallySurjective.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.

Section EnrichedRezkCompletionUMP.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {C₃ : univalent_category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (EF : functor_enrichment F E₁ E₂)
          (HF₁ : essentially_surjective F)
          (HF₂ : fully_faithful_enriched_functor EF).

  (** * 1. Universal property of the Rezk completion *)
  Definition enriched_rezk_completion_ump
    : adj_equivalence_of_cats (enriched_precomp E₃ EF).
  Proof.
    use rad_equivalence_of_cats.
    - use is_univalent_enriched_functor_cat.
      apply univalent_category_is_univalent.
    - apply (enriched_rezk_completion_ump_fully_faithful EF HF₁ HF₂).
    - exact (enriched_rezk_completion_ump_essentially_surjective EF HF₁ HF₂).
  Defined.

  Let L : enriched_functor_category E₂ E₃ ⟶ enriched_functor_category E₁ E₃
    := enriched_precomp E₃ EF.
  Let R : enriched_functor_category E₁ E₃ ⟶ enriched_functor_category E₂ E₃
    := right_adjoint enriched_rezk_completion_ump.
  Let ε : nat_z_iso (R ∙ L) (functor_identity _)
    := counit_nat_z_iso_from_adj_equivalence_of_cats
         enriched_rezk_completion_ump.
  Let η : nat_z_iso (functor_identity _) (L ∙ R)
    := unit_nat_z_iso_from_adj_equivalence_of_cats
         enriched_rezk_completion_ump.

  Let FF : enriched_functor_category E₁ E₂ := F ,, EF.

  (** * 2. Accessors for the universal property of the Rezk completion *)
  Definition lift_enriched_functor_along
             (G : enriched_functor_category E₁ E₃)
    : enriched_functor_category E₂ E₃
    := R G.

  Definition lift_enriched_functor_along_comm
             (G : enriched_functor_category E₁ E₃)
    : z_iso
        (comp_enriched_functor_category FF (lift_enriched_functor_along G))
        G.
  Proof.
    exact (nat_z_iso_pointwise_z_iso ε G).
  Defined.

  Definition lift_enriched_nat_trans_along
             {G₁ G₂ : enriched_functor_category E₂ E₃}
             (α : comp_enriched_functor_category FF G₁
                  -->
                  comp_enriched_functor_category FF G₂)
    : G₁ --> G₂.
  Proof.
    exact (invmap
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   enriched_rezk_completion_ump
                   G₁ G₂))
             α).
  Defined.

  Definition lift_enriched_nat_trans_along_comm
             {G₁ G₂ : enriched_functor_category E₂ E₃}
             (α : comp_enriched_functor_category FF G₁
                  -->
                  comp_enriched_functor_category FF G₂)
    : pre_whisker_enriched_functor_category
        FF
        (lift_enriched_nat_trans_along α) = α.
  Proof.
    exact (homotweqinvweq
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   enriched_rezk_completion_ump
                   G₁ G₂))
             α).
  Qed.

  Definition lift_enriched_nat_trans_eq_along
             {G₁ G₂ : enriched_functor_category E₂ E₃}
             {β₁ β₂ : G₁ --> G₂}
             (p : pre_whisker_enriched_functor_category FF β₁
                  =
                  pre_whisker_enriched_functor_category FF β₂)
    : β₁ = β₂.
  Proof.
    exact (maponpaths
             pr1
             (proofirrelevance
                _
                (pr2 (fully_faithful_implies_full_and_faithful
                        _ _ _
                        (fully_faithful_from_equivalence
                           _ _ _
                           enriched_rezk_completion_ump))
                   G₁ G₂
                   (pre_whisker_enriched_functor_category FF β₂))
                (β₁ ,, p)
                (β₂ ,, idpath _))).
  Qed.
End EnrichedRezkCompletionUMP.
