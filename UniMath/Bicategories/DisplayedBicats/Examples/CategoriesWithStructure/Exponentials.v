(**
   Bicategory Of Cartesian Closed Categories

  In this file, we construct the (displayed) bicategory [disp_bicat_exponentials] whose objects are categories equipped with chosen binary products and exponentials, and whose morphisms are functors that preserve binary products and exponentials.
  We furthermore define the bicategory of finitely complete cartesian closed categories.

  Contents.
  1. Definition of the bicategory of cartesian closed categories [disp_bicat_exponentials]
  2. Definition of the bicategory of finitely complete cartesian closed categories [disp_bicat_exponentials_over_lim]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.BinProducts.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.

Local Open Scope cat.

Section CategoriesWithExponentials.

  Definition disp_bicat_exponentials'
    : disp_bicat (total_bicat disp_bicat_binproducts).
  Proof.
    use disp_subbicat.
    - exact (λ C, Exponentials (pr12 C)).
    - exact (λ C₁ C₂ E₁ E₂ F, preserves_exponentials E₁ E₂ (pr22 F)).
    - exact (λ C _, id_preserves_exponentials _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, comp_preserves_exponentials HF HG).
  Defined.

  Lemma disp_2cells_iscontr_exponentials'
    : disp_2cells_iscontr disp_bicat_exponentials'.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

  Definition disp_bicat_exponentials
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_exponentials'.

  Lemma disp_2cells_iscontr_exponentials
    : disp_2cells_iscontr disp_bicat_exponentials.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_binproducts.
    - apply disp_2cells_iscontr_exponentials'.
  Qed.

End CategoriesWithExponentials.

Section FinitelyCompleteCategoriesWithExponentials.

  Definition disp_bicat_exponentials_over_lim
    : disp_bicat (total_bicat disp_bicat_limits).
  Proof.
    use disp_subbicat.
    - exact (λ C, Exponentials (pr1 (pr122 C))).
    - exact (λ _ _ E₁ E₂ F, preserves_exponentials E₁ E₂ (pr21 (pr22 F))).
    - exact (λ C _, id_preserves_exponentials _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, comp_preserves_exponentials HF HG).
  Defined.

  Lemma disp_2cells_iscontr_exponentials_over_lim
    : disp_2cells_iscontr disp_bicat_exponentials_over_lim.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_fullsubbicat.
    - apply disp_2cells_iscontr_sub1cell_bicat.
  Qed.



End FinitelyCompleteCategoriesWithExponentials.
