(*
  In this file, we construct bicategories whose objects are categories with equalizers, and whose morphisms suitably preserve equalizers.
  (See [Bicategories/DisplayedBicats/Examples/CategoriesWithStructure/FiniteLimits.v] for more details.)

  Contents:
  - [disp_bicat_chosen_equalizers] is the (displayed) bicategory whose objects are categories *equipped with chosen* equalizers, and whose morphisms are functors that *preserve the chosen* equalizers up to an equality. (The equality is surrounded by a truncation to enforce that the preservation is a proposition.)

  - [disp_bicat_have_equalizers] is the (displayed) bicategory whose objects are categories for which there *merely exists* equalizers, and whose morphisms are functors that *preserve any chosen* equalizers.

  - [disp_bicat_equalizers] is the (displayed) bicategory whose objects are the same as in [disp_bicat_chosen_equalizers], and whose morphisms are the same as in [disp_bicat_have_equalizers].
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.

Local Open Scope cat.

Section CategoriesWithChosenEqualizersAndPreservationUpToEquality.

  Definition disp_bicat_chosen_equalizers
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Equalizers C).
    - exact (λ C₁ C₂ BP₁ BP₂ F, preserves_chosen_equalizers_eq F BP₁ BP₂).
    - exact (λ C T, identity_preserves_chosen_equalizers_eq T).
    - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_equalizers_eq PF PG).
  Defined.

  Definition cat_with_chosen_equalizers
    : bicat
    := total_bicat disp_bicat_chosen_equalizers.

  Lemma disp_2cells_iscontr_chosen_equalizers
    : disp_2cells_iscontr disp_bicat_chosen_equalizers.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenEqualizersAndPreservationUpToEquality.

Section CategoriesWithExistingEqualizersAndPreservationIsCreation.

  Definition disp_bicat_have_equalizers
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, hasEqualizers (C := C)).
    - exact (λ C₁ C₂ _ _ F, preserves_equalizer F).
    - exact (λ C _, identity_preserves_equalizer _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_equalizer HF HG).
  Defined.

  Definition cat_with_equalizers
    : bicat
    := total_bicat disp_bicat_have_equalizers.

  Lemma disp_2cells_iscontr_have_equalizers
    : disp_2cells_iscontr disp_bicat_have_equalizers.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithExistingEqualizersAndPreservationIsCreation.

Section CategoriesWithChosenEqualizersAndPreservationIsCreation.

  Definition disp_bicat_equalizers
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Equalizers C).
    - exact (λ C₁ C₂ _ _ F, preserves_equalizer F).
    - exact (λ C _, identity_preserves_equalizer _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_equalizer HF HG).
  Defined.

  Lemma disp_2cells_iscontr_equalizers
    : disp_2cells_iscontr disp_bicat_equalizers.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenEqualizersAndPreservationIsCreation.
