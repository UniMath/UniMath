(*
In this file, we show how the Rezk completion for finitely complete categories lifts to those equipped with a subobject classifier.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.SubobjectClassifier.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.SubobjectClassifier.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.SubobjectClassifier.

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

Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.SubobjectClassifier.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteLimits.

Local Open Scope cat.

Section CategoriesSubobjectClassifierAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_subobject_classifier_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_subobject_classifier.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_limits_has_RC _ η_weak_equiv).
    - simpl ; intros C₁ C₂ C₂_univ F F_weq [[T₁ ?] [BP₁ ?]] [Ω₁ ?].
      refine (_ ,, tt).
      apply (weak_equiv_creates_subobject_classifier _ _ Ω₁).
    - cbn ; intros C [[T ?] [BP ?]] [Ω ?].
      refine (tt ,, _).
      apply weak_equiv_preserves_subobject_classifier.
    - cbn ; intros C₁ C₂ C₃ F G H n
        [[T₁ ?] [BP₁ ?]] [Ω₁ _]
        [[T₂ ?] [BP₂ ?]] [Ω₂ _]
        [[T₃ ?] [BP₃ ?]] [Ω₃ _]
        G_weq
        [[? Fpt] [? Fpb]]
        [? FΩ].
      refine (tt ,, _).
      use preserves_subobject_classifier_independent_of_chosen_terminal_if_univalent.
      + exact (weak_equiv_creates_terminal G_weq T₁).
      + exact (weak_equiv_lifts_preserves_subobject_classifier C₂ C₃ n G_weq Fpt T₁ T₃ FΩ).
      + apply C₂.
  Defined.

  Theorem disp_bicat_subobject_classifier_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_subobject_classifier.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_subobject_classifier_has_RC.
    - apply disp_2cells_iscontr_subobject_classifier.
  Defined.

End CategoriesSubobjectClassifierAdmitRezkCompletions.
