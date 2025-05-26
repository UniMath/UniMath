(*
Lifting of Rezk completions to categories with a parameterized NNO.

In this file, we show how the Rezk completion for finitely complete categories lifts to those equipped with a parameterized natural numbers object.

Contents.
1. The lifted biadjoint [disp_bicat_parameterized_NNO_has_Rezk_completion]
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.PNNO.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.ParameterizedNNO.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteLimits.

Local Open Scope cat.

Section CategoriesNNOAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_parameterized_NNO_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_parameterized_NNO.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_limits_has_RC _ η_weak_equiv).
    - simpl ; intros C₁ C₂ C₂_univ F F_weq ? [N₁ ?].
      refine (_ ,, tt).
      apply (weak_equiv_creates_parameterized_NNO F_weq N₁).
    - cbn ; intros C [[T ?] [BP ?]] [Ω ?].
      refine (tt ,, _).
      apply weak_equiv_preserves_parameterized_NNO'.
    - cbn ; intros C₁ C₂ C₃ F G H α
        ? [N₁ ?]
        ? [N₂ ?]
        ? [N₃ ?]
        G_weq
        ?
        [? FN].
      refine (tt ,, _).
      exact (weak_equiv_lifts_preserves_parameterized_NNO α G_weq N₁ N₂ N₃ FN).
  Defined.

  Theorem disp_bicat_parameterized_NNO_has_Rezk_completion
    : cat_with_structure_has_RezkCompletion disp_bicat_parameterized_NNO.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_parameterized_NNO_has_RC.
    - apply disp_2cells_iscontr_parameterized_NNO.
  Defined.

End CategoriesNNOAdmitRezkCompletions.
