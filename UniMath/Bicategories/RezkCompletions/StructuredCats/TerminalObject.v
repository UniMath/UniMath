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

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_have_terminal_obj.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_terminal_obj)).

  Definition cat_with_terminal_obj_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw C1_term.
      refine (_ ,, tt).
      use (factor_through_squash _ _ (pr1 C1_term)).
      { apply isapropishinh. }
      clear C1_term.
      intro C1_term.
      apply hinhpr.
      set (t := weak_equiv_preserves_chosen_terminal _ Fw C1_term).
      exact (F C1_term ,, t).
    - intros C C1_term.
      refine (tt ,, _).
      use (factor_through_squash _ _ (pr1 C1_term)).
      { apply isaprop_preserves_terminal. }
      intro C1_term'.
      use weak_equiv_preserves_terminal.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fpterm].
      exists tt.
      exact (weak_equiv_lifts_preserves_terminal α Gw Fpterm).
  Defined.

End BicatOfCategoriesWithTerminalHasRezkCompletion.

Section BicatOfCategoriesWithChosenTerminalHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_chosen_terminal_obj.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_terminal_obj)).

  Definition cat_with_chosen_terminal_obj_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw C1_term.
      refine (_ ,, tt).
      set (t := weak_equiv_preserves_chosen_terminal _ Fw (pr1 C1_term)).
      exact (F (pr11 C1_term) ,, t).
    - intros C C1_term.
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
