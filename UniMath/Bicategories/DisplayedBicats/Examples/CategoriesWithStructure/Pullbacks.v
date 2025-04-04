Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.

Local Open Scope cat.

Section CategoriesWithChosenPullbacksAndPreservationUpToEquality.

  Definition disp_bicat_chosen_pullbacks
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Pullbacks C).
    - exact (λ C₁ C₂ BP₁ BP₂ F, preserves_chosen_pullbacks_eq F BP₁ BP₂).
    - exact (λ C T, identity_preserves_chosen_pullbacks_eq T).
    - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_pullbacks_eq PF PG).
  Defined.

  Definition cat_with_chosen_pullbacks
    : bicat
    := total_bicat disp_bicat_chosen_pullbacks.

  Lemma disp_2cells_iscontr_chosen_pullbacks
    : disp_2cells_iscontr disp_bicat_chosen_pullbacks.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
  Qed.

End CategoriesWithChosenPullbacksAndPreservationUpToEquality.

Section CategoriesWithExistingPullbacksAndPreservationIsCreation.

  Definition disp_bicat_have_pullbacks
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, hasPullbacks C).
    - exact (λ C₁ C₂ _ _ F, preserves_pullback F).
    - exact (λ C _, identity_preserves_pullback _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
  Defined.

  Definition cat_with_pullbacks
    : bicat
    := total_bicat disp_bicat_have_pullbacks.

  Lemma disp_2cells_iscontr_have_pullbacks
    : disp_2cells_iscontr disp_bicat_have_pullbacks.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
  Qed.

End CategoriesWithExistingPullbacksAndPreservationIsCreation.

Section CategoriesWithChosenPullbacksAndPreservationIsCreation.

  Definition disp_bicat_pullbacks
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Pullbacks C).
    - exact (λ C₁ C₂ _ _ F, preserves_pullback F).
    - exact (λ C _, identity_preserves_pullback _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
  Defined.

  Lemma disp_2cells_iscontr_pullbacks
    : disp_2cells_iscontr disp_bicat_pullbacks.
  Proof.
    intro ; intros.
    exists (tt,,tt).
    intro.
    use total2_paths_f ; apply iscontrunit.
  Qed.

End CategoriesWithChosenPullbacksAndPreservationIsCreation.
