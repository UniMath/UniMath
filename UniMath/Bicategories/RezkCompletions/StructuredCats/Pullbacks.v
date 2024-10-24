(*
In this file, we show how the Rezk completion of a categories has a suitable terminal object (in terms of preservation) if the original category has a terminal object.
Hence, categories with terminal objects admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a terminal object (up to propositional truncation).
2. BicatOfCategoriesWithChosenTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a chosen terminal object.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Pullbacks.


Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Local Open Scope cat.

Section CategoriesWithPullbacksAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Definition cat_with_pullback_has_RezkCompletion
    : disp_left_universal_arrow
        LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_have_pullbacks
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_pullbacks)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw [P1 _].
      exact (weak_equiv_into_univ_creates_pullbacks C2_univ Fw P1 ,, tt).
    - intros C pb.
      refine (tt ,, _).
      apply weak_equiv_preserves_pullbacks.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α ? ? ? Gw.
      intros [t Fpb].
      exists tt.
      use (weak_equiv_lifts_preserves_pullbacks C2 C3 α Gw Fpb).
  Qed.

  Definition cat_with_chosen_pullbacks_has_RezkCompletion
    : disp_left_universal_arrow
        LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_chosen_pullbacks
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_pullbacks)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw P1.
      exact (weak_equiv_into_univ_creates_pullbacks C2_univ Fw (pr1 P1) ,, tt).
    - intros C P1.
      refine (tt ,, _).
      use weak_equiv_preserves_pullbacks_eq.
      + apply η_weak_equiv.
      + exact (pr2 (pr1 LUR C)).
    - intros C1 C2 C3 F G H α P1 P2 P3 Gw.
      intros [t Fprod].
      exists tt.
      exact (weak_equiv_lifts_preserves_chosen_pullbacks_eq C2 C3 α (pr1 P1) (pr1 P2) (pr1 P3) Gw Fprod).
  Defined.

End CategoriesWithPullbacksAdmitRezkCompletions.
