(*
In this file, we show how the Rezk completion of a categories has a suitable terminal object (in terms of preservation) if the original category has a terminal object.
Hence, categories with terminal objects admit a Rezk completion.

Contents:
1. [BicatOfCategoriesWithTerminalHasRezkCompletion]
   A construction of the Rezk completion of categories (merely) having a terminal object.
2. [BicatOfCategoriesWithChosenTerminalHasRezkCompletion]
   A construction of the Rezk completion of categories equipped with a chosen terminal object.
3. [CategoriesWithChosenTerminalAndPreservationIsCreationHasRezkCompletions]
   A construction of the Rezk completion for categories equipped with a chosen terminal object.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Terminal.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.

Local Open Scope cat.

Section BicatOfCategoriesWithTerminalHasRezkCompletion.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_have_terminal_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_have_terminal.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F F_weq [T1 _].
      refine (_ ,, tt).
      use (factor_through_squash _ _ T1).
      { apply isapropishinh. }
      clear T1.
      intro T1.
      apply hinhpr.
      exact (weak_equiv_creates_terminal F_weq T1).
    - intros C [T1 ?].
      refine (tt ,, _).
      use weak_equiv_preserves_terminal.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fpterm].
      exists tt.
      exact (weak_equiv_lifts_preserves_terminal α Gw Fpterm).
  Defined.

  Corollary disp_bicat_have_terminal_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_have_terminal.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_have_terminal_has_RC).
    exact disp_2cells_iscontr_have_terminal.
  Defined.

End BicatOfCategoriesWithTerminalHasRezkCompletion.

Section BicatOfCategoriesWithChosenTerminalHasRezkCompletion.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_chosen_terminal_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_chosen_terminal.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F F_weq [T1 _].
      exact (weak_equiv_creates_terminal F_weq T1 ,, tt).
    - intros C [T1 ?].
      refine (tt ,, _).
      apply hinhpr.
      apply idpath.
    - intros C1 C2 C3 F G H α C1_term C2_term C3_term Gw.
      intros [t Fpterm].
      exists tt.
      use (factor_through_squash _ _ Fpterm).
      { apply isapropishinh. }
      intro p.

      set (Gpterm := weak_equiv_preserves_chosen_terminal_eq _ Gw (pr2 C2) (pr1 C1_term) (pr1 C2_term)).
      use (factor_through_squash _ _ Gpterm).
      { apply isapropishinh. }
      intro q.

      apply hinhpr.
      refine (_ @ p).
      etrans. {
        apply maponpaths, (! q).
      }
      apply C3.
      simpl in C1_term
      ; exact (_ ,, pr2 α (pr1 C1_term)).
  Defined.

  Corollary disp_bicat_chosen_terminal_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_chosen_terminal.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_chosen_terminal_has_RC).
    exact disp_2cells_iscontr_chosen_terminal.
  Defined.

End BicatOfCategoriesWithChosenTerminalHasRezkCompletion.

Section CategoriesWithChosenTerminalAndPreservationIsCreationHasRezkCompletions.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_terminal_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_terminal.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [T1 _].
      exact (make_Terminal _ (weak_equiv_preserves_terminal _ Fw _ (pr2 T1)) ,, tt).
    - intros C [T1 ?].
      refine (tt ,, _).
      use weak_equiv_preserves_terminal.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fpterm].
      exists tt.
      exact (weak_equiv_lifts_preserves_terminal α Gw Fpterm).
  Defined.

  Corollary disp_bicat_terminal_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_terminal.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_terminal_has_RC).
    exact disp_2cells_iscontr_terminal.
  Defined.

End CategoriesWithChosenTerminalAndPreservationIsCreationHasRezkCompletions.
