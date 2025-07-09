(**
  In this file, we construct the (displayed) bicategory [disp_bicat_exponentials] whose objects are categories equipped with chosen binary products and exponentials, and whose morphisms are functors that preserve binary products and exponentials.
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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.BinProducts.

Local Open Scope cat.

Section CategoriesWithExponentials.

  Definition disp_bicat_exponentials'
    : disp_bicat (total_bicat disp_bicat_binproducts).
  Proof.
    use disp_subbicat.
    - exact (λ C, Exponentials (pr12 C)).
    - exact (λ C₁ C₂ E1 E2 F, preserves_exponentials E1 E2 (pr22 F)).
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
