(********************************************************************************

 Precomposition

 In this file, we define the precomposition functor for enriched categories.
 More specifically, given an enriched functor from `C₁` to `C₂`, we get a functor
 from the category `E₂ ⟶ E₃` of enriched functors to the category `E₁ ⟶ E₃`
 of enriched functors. Note that we do not require these two categories to be
 enriched. We are only interested in them as categories.

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.

Section Precomp.
  Context {V : monoidal_cat}
          {C₁ C₂ C₃ : category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (E₃ : enrichment C₃ V)
          (EF : functor_enrichment F E₁ E₂).

  Definition enriched_precomp_data
    : functor_data
        (enriched_functor_category E₂ E₃)
        (enriched_functor_category E₁ E₃).
  Proof.
    use make_functor_data.
    - exact (λ G, F ∙ _ ,, functor_comp_enrichment EF (pr2 G)).
    - exact (λ _ _ τ, pre_whisker F (pr1 τ) ,, pre_whisker_enrichment EF (pr2 τ)).
  Defined.

  Proposition is_functor_enriched_precomp
    : is_functor enriched_precomp_data.
  Proof.
    split.
    - intros G.
      use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ].
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      apply idpath.
    - intros G₁ G₂ G₃ τ₁ τ₂.
      use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ].
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      apply idpath.
  Qed.

  Definition enriched_precomp
    : enriched_functor_category E₂ E₃
      ⟶
      enriched_functor_category E₁ E₃.
    Proof.
      use make_functor.
      - exact enriched_precomp_data.
      - exact is_functor_enriched_precomp.
    Defined.
End Precomp.
