(*
  In this file, we construct bicategories whose objects are categories with binary products, and whose morphisms suitably preserve binary products.
  (See [Bicategories/DisplayedBicats/Examples/CategoriesWithStructure/FiniteLimits.v] for more details.)

  Contents:
  - [disp_bicat_chosen_binproducts] is the (displayed) bicategory whose objects are categories *equipped with chosen* binary products, and whose morphisms are functors that *preserve the chosen* products up to an equality. (The equality is surrounded by a truncation to enforce that the preservation is a proposition.)

  - [disp_bicat_have_binproducts] is the (displayed) bicategory whose objects are categories for which there *merely exists* binary products, and whose morphisms are functors that *preserve any chosen* binary products.

  - [disp_bicat_binproducts] is the (displayed) bicategory whose objects are the same as in [disp_bicat_chosen_binproducts], and whose morphisms are the same as in [disp_bicat_have_binproducts].
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.

Local Open Scope cat.

Section CategoriesWithChosenBinProductsAndPreservationUpToEquality.

  Definition disp_bicat_chosen_binproducts
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, BinProducts C).
    - exact (λ C₁ C₂ BP₁ BP₂ F, preserves_chosen_binproducts_eq F BP₁ BP₂).
    - exact (λ C T, identity_preserves_chosen_binproducts_eq T).
    - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_binproducts_eq PF PG).
  Defined.

  Definition cat_with_chosen_binproducts
    : bicat
    := total_bicat disp_bicat_chosen_binproducts.

  Lemma disp_2cells_iscontr_chosen_binproducts
    : disp_2cells_iscontr disp_bicat_chosen_binproducts.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenBinProductsAndPreservationUpToEquality.

Section CategoriesWithExistingBinProductsAndPreservationIsCreation.

  Definition disp_bicat_have_binproducts
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, hasBinProducts C).
    - exact (λ C₁ C₂ _ _ F, preserves_binproduct F).
    - exact (λ C _, identity_preserves_binproduct _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_binproduct HF HG).
  Defined.

  Definition cat_with_binproducts
    : bicat
    := total_bicat disp_bicat_have_binproducts.

  Lemma disp_2cells_iscontr_have_binproducts
    : disp_2cells_iscontr disp_bicat_have_binproducts.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithExistingBinProductsAndPreservationIsCreation.

Section CategoriesWithChosenBinProductsAndPreservationIsCreation.

  Definition disp_bicat_binproducts
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, BinProducts C).
    - exact (λ C₁ C₂ _ _ F, preserves_binproduct F).
    - exact (λ C _, identity_preserves_binproduct _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_binproduct HF HG).
  Defined.

  Lemma disp_2cells_iscontr_binproducts : disp_2cells_iscontr disp_bicat_binproducts.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenBinProductsAndPreservationIsCreation.
