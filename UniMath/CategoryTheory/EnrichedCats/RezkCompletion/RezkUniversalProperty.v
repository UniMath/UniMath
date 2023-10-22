(********************************************************************************

 The universal property of the enriched Rezk completion

 To prove the universal property of the Rezk completion of enriched categories,
 we need to prove that precomposition with a weak equivalence gives rise to an
 adjoint equivalence between functor categories to univalent categories. To prove
 this statement, we show that this precomposition functor is both fully faithful
 and essentially surjective. This file contains the statement that precomposition
 with a fully faithful and essential surjective enriched functor is an adjoint
 equivalence ([enriched_rezk_completion_ump]).

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Precomposition.
Require Export UniMath.CategoryTheory.EnrichedCats.RezkCompletion.PrecompFullyFaithful.
Require Export UniMath.CategoryTheory.EnrichedCats.RezkCompletion.PrecompEssentiallySurjective.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.

Definition enriched_rezk_completion_ump
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {C₃ : univalent_category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (EF : functor_enrichment F E₁ E₂)
           (HF₁ : essentially_surjective F)
           (HF₂ : fully_faithful_enriched_functor EF)
  : adj_equivalence_of_cats (enriched_precomp E₃ EF).
Proof.
  use rad_equivalence_of_cats.
  - use is_univalent_enriched_functor_cat.
    apply univalent_category_is_univalent.
  - use full_and_faithful_implies_fully_faithful.
    split.
    + exact (enriched_rezk_completion_ump_full EF HF₁ HF₂).
    + exact (enriched_rezk_completion_ump_faithful EF HF₁).
  - exact (enriched_rezk_completion_ump_essentially_surjective EF HF₁ HF₂).
Defined.
