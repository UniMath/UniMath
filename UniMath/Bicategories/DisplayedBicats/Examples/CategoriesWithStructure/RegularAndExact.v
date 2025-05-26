(*

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.

Local Open Scope cat.

Section RegularCategories.

  Definition disp_bicat_regular'
    : disp_bicat (total_bicat disp_bicat_limits).
  Proof.
    use disp_subbicat.
    - exact (λ C, coeqs_of_kernel_pair (pr1 C) × RegularEpi.regular_epi_pb_stable (pr1 C)).
    - exact (λ C₁ C₂ _ _ F, preserves_regular_epi (pr1 F)).
    - exact (λ _ _, id_preserves_regular_epi _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, comp_preserves_regular_epi HF HG).
  Defined.

  Lemma disp_2cells_iscontr_regular'
    : disp_2cells_iscontr disp_bicat_regular'.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

  Definition disp_bicat_regular
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_regular'.

  Lemma disp_2cells_iscontr_regular
    : disp_2cells_iscontr disp_bicat_regular.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_limits.
    - apply disp_2cells_iscontr_regular'.
  Qed.

End RegularCategories.

Section ExactCategories.

  Definition disp_bicat_exact'
    : disp_bicat (total_bicat disp_bicat_regular).
  Proof.
    use disp_fullsubbicat.
    exact (λ C, all_internal_eqrel_effective (pr1 C)).
  Defined.

  Lemma disp_2cells_iscontr_exact'
    : disp_2cells_iscontr disp_bicat_exact'.
  Proof.
    intro ; intros ; apply iscontrunit.
  Qed.

  Definition disp_bicat_exact
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_exact'.

  Lemma disp_2cells_iscontr_exact
    : disp_2cells_iscontr disp_bicat_exact.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_regular.
    - apply disp_2cells_iscontr_exact'.
  Qed.

End ExactCategories.
