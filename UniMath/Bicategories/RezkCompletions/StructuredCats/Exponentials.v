(**
In this file, we show how the Rezk completion for categories with binary products lifts to those equipped with exponentials.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Exponentials.

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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Exponentials.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.BinProducts.

Local Open Scope cat.

Section CategoriesExponentialsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_exponentials_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_exponentials.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_binproducts_has_RC η_weak_equiv).
    - simpl ; intros C₁ C₂ C₂_univ F F_weq [P₁ ?] [E₁ ?].
      refine (_ ,, tt).
      apply (weak_equiv_into_univ_creates_exponentials F_weq C₂_univ E₁).
    - cbn ; intros C [P ?] [E ?].
      refine (tt ,, _).
      apply weak_equiv_preserves_exponentials.
    - cbn ; intros C₁ C₂ C₃ F G H n
              [P₁ ?] [E₁ ?] [P₂ ?] [E₂ ?] [P₃ ?] [E₃ ?]
              G_weq
              [? F_pP] [? F_pE].
      refine (tt ,, _).
      exact (weak_equiv_lifts_preserves_exponentials' C₂ C₃ n E₁ E₂ E₃ G_weq F_pE).
  Defined.

  Theorem disp_bicat_exponential_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_exponentials.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_exponentials_has_RC.
    - apply disp_2cells_iscontr_exponentials.
  Defined.

End CategoriesExponentialsAdmitRezkCompletions.
