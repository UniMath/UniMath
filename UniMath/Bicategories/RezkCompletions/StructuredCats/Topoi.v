(**
   Rezk Completions For Topoi

   In this file, we show how the Rezk completion for categories lifts to the following types of topoi: elementary topoi, and arithmetic topoi.

   Contents.
   1. [disp_bicat_elementarytopoi_has_RezkCompletion] proves the lifting to elementary topoi
   2. [disp_bicat_arithmetic_elementarytopoi_has_RezkCompletion] proves the lifting to elementary with a parameterized NNO.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.SubobjectClassifier.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.SubobjectClassifier.
Require Import UniMath.CategoryTheory.WeakEquivalences.PNNO.

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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Topoi.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteLimits.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.RegularAndExact.

Local Open Scope cat.

(** * 1. Lifting Of Rezk Completions To Elementary Topoi *)
Section ElementaryTopoiAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_elementarytopoi_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_elementarytopoi.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma.
    - exact (disp_bicat_limits_has_RC LUR η_weak_equiv).
    - simpl.
      intros C₁ C₂ C₂_univ F F_weq L₁ [[E₁ ?] [Ω₁ ?]].
      refine ((_ ,, tt) ,, (_ ,, tt)).
      + apply (weak_equiv_into_univ_creates_exponentials F_weq C₂_univ E₁).
      + apply (weak_equiv_creates_subobject_classifier F_weq _ Ω₁).
    - intros C L₁ [[E₁ ?] [Ω₁ ?]].
      refine ((tt ,, _) ,, (tt ,, _)).
      + apply weak_equiv_preserves_exponentials.
      + apply weak_equiv_preserves_subobject_classifier.
    - simpl.
      intros C₁ C₂ C₃ F G H n
        L₁ [[E₁ ?] [Ω₁ ?]]
        L₂ [[E₂ ?] [Ω₂ ?]]
        L₃ [[E₃ ?] [Ω₃ ?]]
        G_weq F_pL [[? F_pexp] [? F_Ω]].
      refine ((tt ,, _) ,, (tt ,, _)).
      + use (weak_equiv_lifts_preserves_exponentials').
        * exact (pr112 L₁).
        * exact E₁.
        * exact F_pexp.
      + use preserves_subobject_classifier_independent_of_chosen_terminal_if_univalent.
        * apply (weak_equiv_creates_terminal G_weq (pr11 L₁)).
        * apply weak_equiv_lifts_preserves_subobject_classifier.
          exact F_Ω.
        * apply C₂.
  Defined.

  Theorem disp_bicat_elementarytopoi_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_elementarytopoi.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_elementarytopoi_has_RC.
    - apply disp_bicat_elementarytopoi_is_locally_contractible.
  Defined.

End ElementaryTopoiAdmitRezkCompletions.

(** * 2. Lifting Of Rezk Completions To Arithmetic Topoi *)
Section ArithmeticTopoiAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_arithmetic_elementarytopoi_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_arithmetic_elementarytopoi.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma.
    - exact (disp_bicat_elementarytopoi_has_RC LUR η_weak_equiv).
    - simpl.
      intros ? ? ? ? F_weq ? [N₁ ?].
      refine (_ ,, tt).
      apply (weak_equiv_creates_parameterized_NNO F_weq N₁).
    - intro ; intros.
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

  Theorem disp_bicat_arithmetic_elementarytopoi_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_arithmetic_elementarytopoi.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_arithmetic_elementarytopoi_has_RC.
    - apply disp_bicat_arithmetic_elementarytopoi_is_locally_contractible.
  Defined.

End ArithmeticTopoiAdmitRezkCompletions.
