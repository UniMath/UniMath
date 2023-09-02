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
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.CategoryTheory.WeakEquivalences.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.Preservation.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

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
    - intros C1 C2 C3 F G H α C1_term C2_term C3_term Gw.
      intros [t Fpterm].
      exists tt.
      intros x2 x2_is_term.
      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x2)).
      { apply isaprop_isTerminal. }
      intros [x1 i] y3.
      use (iscontrweqb' (Y :=  (pr1 C3⟦y3, H(G x1)⟧))).
      + use (iscontrweqb' (Y := (pr1 C3⟦y3, F x1⟧))).
        * use (Fpterm _ _).
          use (weak_equiv_reflects_terminal _ Gw).
          exact (iso_to_Terminal (_,, x2_is_term) _ (z_iso_inv i)).
        * apply z_iso_comp_left_weq.
          exact (_ ,, pr2 α x1).
      + apply z_iso_comp_left_weq.
        apply functor_on_z_iso.
        exact (z_iso_inv i).
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
