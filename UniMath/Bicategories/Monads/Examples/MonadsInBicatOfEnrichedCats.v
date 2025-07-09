(**********************************************************************

 Monads in the bicategory of enriched categories

 We give some useful statements when using monads internal to the
 bicategory of enriched categories.

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfUnivCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInTotalBicat.

Local Open Scope cat.

Section EnrichmentMonads.
  Context (V : monoidal_cat).

  Definition make_mnd_enriched_cats
             {C : univalent_category}
             (E : enrichment C V)
             (M : Monad C)
             (EM : monad_enrichment E M)
    : mnd (bicat_of_enriched_cats V).
  Proof.
    use make_mnd_total_bicat.
    - apply disp_2cell_isapprop_enriched_cats.
    - exact (Monad_to_mnd_bicat_of_univ_cats M).
    - use make_disp_mnd ; cbn.
      + exact E.
      + exact EM.
      + exact (unit_of_monad_enrichment EM).
      + exact (mu_of_monad_enrichment EM).
  Defined.

  Definition Monad_from_mnd_enriched_cats
             (M : mnd (bicat_of_enriched_cats V))
    : Monad (pr11 (ob_of_mnd M))
    := mnd_bicat_of_univ_cats_to_Monad (pr1_of_mnd_total_bicat M).

  Definition Monad_enrichment_from_mnd_enriched_cats
             (M : mnd (bicat_of_enriched_cats V))
    : monad_enrichment
        (pr2 (ob_of_mnd M))
        (Monad_from_mnd_enriched_cats M).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (pr2 (endo_of_mnd M)).
    - exact (pr2 (unit_of_mnd M)).
    - exact (pr2 (mult_of_mnd M)).
  Defined.

  Section MonadMorProjections.
    Context {m₁ m₂ : mnd (bicat_of_enriched_cats V)}
            (f : m₁ --> m₂).

    Let C₁ : univalent_category := pr1 (ob_of_mnd m₁).
    Let C₂ : univalent_category := pr1 (ob_of_mnd m₂).
    Let M₁ : Monad C₁ := Monad_from_mnd_enriched_cats m₁.
    Let M₂ : Monad C₂ := Monad_from_mnd_enriched_cats m₂.
    Let η₁ : functor_identity _ ⟹ M₁ := pr1 (unit_of_mnd m₁).
    Let η₂ : functor_identity _ ⟹ M₂ := pr1 (unit_of_mnd m₂).
    Let μ₁ : M₁ ∙ M₁ ⟹ M₁ := pr1 (mult_of_mnd m₁).
    Let μ₂ : M₂ ∙ M₂ ⟹ M₂ := pr1 (mult_of_mnd m₂).
    Let F : C₁ ⟶ C₂ := pr1 (mor_of_mnd_mor f).
    Let Fm : F ∙ M₂ ⟹ M₁ ∙ F := pr1 (mnd_mor_endo f).

    Definition mnd_mor_unit_enriched
               (x : C₁)
      : #F (η₁ x) = η₂ (F x) · Fm x.
    Proof.
      pose (from_eq_enriched_nat_trans (mnd_mor_unit f) x) as p.
      cbn in p.
      rewrite !id_left in p.
      exact p.
    Qed.

    Definition mnd_mor_mu_enriched
               (x : C₁)
      : #M₂ (Fm x) · Fm (M₁ x) · #F (μ₁ x) = μ₂ (F x) · Fm x.
    Proof.
      pose (from_eq_enriched_nat_trans (mnd_mor_mu f) x) as p.
      cbn in p.
      rewrite !id_left in p.
      rewrite !id_right in p.
      exact p.
    Qed.
  End MonadMorProjections.

  Section MonadCellProjections.
    Context {m₁ m₂ : mnd (bicat_of_enriched_cats V)}
            {f₁ f₂ : m₁ --> m₂}
            (τ : f₁ ==> f₂).

    Let C₁ : univalent_category := pr1 (ob_of_mnd m₁).
    Let C₂ : univalent_category := pr1 (ob_of_mnd m₂).
    Let M₁ : Monad C₁ := Monad_from_mnd_enriched_cats m₁.
    Let M₂ : Monad C₂ := Monad_from_mnd_enriched_cats m₂.
    Let η₁ : functor_identity _ ⟹ M₁ := pr1 (unit_of_mnd m₁).
    Let η₂ : functor_identity _ ⟹ M₂ := pr1 (unit_of_mnd m₂).
    Let μ₁ : M₁ ∙ M₁ ⟹ M₁ := pr1 (mult_of_mnd m₁).
    Let μ₂ : M₂ ∙ M₂ ⟹ M₂ := pr1 (mult_of_mnd m₂).
    Let F₁ : C₁ ⟶ C₂ := pr1 (mor_of_mnd_mor f₁).
    Let Fm₁ : F₁ ∙ M₂ ⟹ M₁ ∙ F₁ := pr1 (mnd_mor_endo f₁).
    Let F₂ : C₁ ⟶ C₂ := pr1 (mor_of_mnd_mor f₂).
    Let Fm₂ : F₂ ∙ M₂ ⟹ M₁ ∙ F₂ := pr1 (mnd_mor_endo f₂).
    Let τc : F₁ ⟹ F₂ := pr1 (cell_of_mnd_cell τ).

    Definition mnd_cell_endo_enriched
               (x : C₁)
      : Fm₁ x · τc (M₁ x) = #M₂ (τc x) · Fm₂ x.
    Proof.
      pose (from_eq_enriched_nat_trans (mnd_cell_endo τ) x) as p.
      exact p.
    Qed.
  End MonadCellProjections.
End EnrichmentMonads.
