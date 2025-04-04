Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.

Local Open Scope cat.

Section LexCategoriesWithChosenSubobjectClassifierAndPreservationIsCreation.

  Definition disp_bicat_subobject_classifier'
    : disp_bicat (total_bicat disp_bicat_limits).
  Proof.
    use disp_subbicat.
    - exact (λ C, subobject_classifier (pr112 C)).
    - exact (λ C₁ C₂ _ _ F, preserves_subobject_classifier (pr1 F) (pr112 C₁) (pr112 C₂) (pr212 F)).
    - exact (λ C _, identity_preserves_subobject_classifier _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, comp_preserves_subobject_classifier HF HG).
  Defined.

  Lemma disp_2cells_iscontr_subobject_classifier'
    : disp_2cells_iscontr disp_bicat_subobject_classifier'.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
  Qed.

  Definition disp_bicat_subobject_classifier
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_subobject_classifier'.

  Lemma disp_2cells_iscontr_subobject_classifier
    : disp_2cells_iscontr disp_bicat_subobject_classifier.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_limits.
    - apply disp_2cells_iscontr_subobject_classifier'.
  Qed.

End LexCategoriesWithChosenSubobjectClassifierAndPreservationIsCreation.
