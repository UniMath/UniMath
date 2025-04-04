(**
In this file, we show how the Rezk completion of a category has equalizers if the original category has equalizers.
Hence, categories with equalizers admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithEqualizersHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with equalizers (up to propositional truncation).
2. BicatOfCategoriesWithChosenEqualizersHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with chosen equalizers.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Equalizers.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Equalizers.

Local Open Scope cat.

Section CategoriesWithEqualizersAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Definition cat_with_equalizers_has_RezkCompletion
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_have_equalizers
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_iscontr_have_equalizers)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw [E₁ _].
      exact (weak_equiv_into_univ_creates_hasequalizers C2_univ Fw E₁ ,, tt).
    - intros C ?.
      refine (tt ,, weak_equiv_preserves_equalizers (η_weak_equiv C)).
    - intros C1 C2 C3 F G H α E₁ E₂ E₃ Gw [t Feq].
      exact (tt ,, weak_equiv_lifts_preserves_equalizers C2 C3 α Gw Feq).
  Defined.

  Definition cat_with_chosen_equalizers_has_RezkCompletion
  : disp_left_universal_arrow LUR
      (disp_psfunctor_on_cat_to_univ_cat disp_bicat_chosen_equalizers
         (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_iscontr_chosen_equalizers)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw C1_prod.
      exact (weak_equiv_into_univ_creates_equalizers C2_univ Fw (pr1 C1_prod) ,, tt).
    - intros C E.
      exists tt.
      apply (weak_equiv_preserves_equalizers_eq (η_weak_equiv C) (pr2 (pr1 LUR C))).
    - intros C1 C2 C3 F G H α E₁ E₂ E₃ Gw.
      intros [t Feq].
      exists tt.
      exact (weak_equiv_lifts_preserves_chosen_equalizers_eq C2 C3 α (pr1 E₁) (pr1 E₂) (pr1 E₃) Gw Feq).
  Defined.

End CategoriesWithEqualizersAdmitRezkCompletions.

Section CategoriesWithChosenEqualizersAndPreservationIsCreationHasRezkCompletions.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_equalizers_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_equalizers.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [E1 ?].
      exact (weak_equiv_into_univ_creates_equalizers C2_univ Fw E1 ,, tt).
    - intros C [E1 ?].
      refine (tt ,, _).
      apply weak_equiv_preserves_equalizers.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α E1 E2 E3 Gw.
      intros [t F_pe].
      exists tt.
      exact (weak_equiv_lifts_preserves_equalizers C2 C3 α Gw F_pe).
  Defined.

  Corollary disp_bicat_equalizers_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_equalizers.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_equalizers_has_RC).
    exact disp_2cells_iscontr_equalizers.
  Defined.

End CategoriesWithChosenEqualizersAndPreservationIsCreationHasRezkCompletions.
