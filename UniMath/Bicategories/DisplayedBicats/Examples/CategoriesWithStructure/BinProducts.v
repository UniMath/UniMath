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

  Lemma disp_2cells_is_contr_chosen_binproducts
    : disp_2cells_iscontr disp_bicat_chosen_binproducts.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
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

  Lemma disp_2cells_is_contr_have_binproducts
    : disp_2cells_iscontr disp_bicat_have_binproducts.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
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
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
  Qed.

End CategoriesWithChosenBinProductsAndPreservationIsCreation.
