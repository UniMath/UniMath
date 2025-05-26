(*
  The Displayed Bicategory Of Categories With A Parameterized Natural Numbers Object

  In this file, we construct the displayed bicategory of finitely complete categories equipped with a natural numbers object.

  Contents
  1. Definition [disp_bicat_parameterized_NNO] and Locally Contractibility [disp_2cells_iscontr_parameterized_NNO]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.

Local Open Scope cat.

(** * 1. Definition And Locally Contractibility *)
Section LexCategoriesWithChosenParameterizedNNOAndPreservationUpToIso.

  Definition disp_bicat_parameterized_NNO'
    : disp_bicat (total_bicat disp_bicat_limits).
  Proof.
    use disp_subbicat.
    - exact (λ C, parameterized_NNO (pr112 C) (pr1 (pr122 C))).
    - exact (λ C₁ C₂ N₁ N₂ F, preserves_parameterized_NNO N₁ N₂ _ (pr212 F)).
    - intro ; intro ; apply id_preserves_parameterized_NNO.
    - exact (λ _ _ _ _ _ _ _ _ p₁ p₂, comp_preserves_parameterized_NNO p₁ p₂).
  Defined.

  Lemma disp_2cells_iscontr_parameterized_NNO'
    : disp_2cells_iscontr disp_bicat_parameterized_NNO'.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

  Definition disp_bicat_parameterized_NNO
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_parameterized_NNO'.

  Lemma disp_2cells_iscontr_parameterized_NNO
    : disp_2cells_iscontr disp_bicat_parameterized_NNO.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_limits.
    - apply disp_2cells_iscontr_parameterized_NNO'.
  Qed.

End LexCategoriesWithChosenParameterizedNNOAndPreservationUpToIso.
