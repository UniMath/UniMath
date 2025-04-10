(*
In this file, we conclude that the Rezk completion for categories lifts to finitely complete categories.

Contents:
1. [CategoriesWithFiniteLimitsAdmitRezkCompletions]
   A construction of the Rezk completion of categories equipped with a terminal object (up to propositional truncation).
2. BicatOfCategoriesWithChosenTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a chosen terminal object.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.Terminal.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.BinProducts.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.Pullbacks.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.Equalizers.

Local Open Scope cat.

Section CategoriesWithChosenFiniteLimitsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_chosen_limits_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_chosen_limits.
  Proof.
    repeat use make_cat_with_struct_has_RC_from_dirprod.
    - apply disp_bicat_chosen_terminal_has_RC.
    - apply disp_bicat_chosen_binproducts_has_RC.
    - apply disp_bicat_chosen_pullbacks_has_RC.
    - apply disp_bicat_chosen_equalizers_has_RC.
  Defined.

  Theorem disp_bicat_chosen_limits_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_chosen_limits.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_chosen_limits_has_RC.
    - exact disp_2cells_iscontr_chosen_limits.
  Defined.

End CategoriesWithChosenFiniteLimitsAdmitRezkCompletions.

Section CategoriesHavingFiniteLimitsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_have_limits_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_have_limits.
  Proof.
    repeat use make_cat_with_struct_has_RC_from_dirprod.
    - apply disp_bicat_have_terminal_has_RC.
    - apply disp_bicat_have_binproducts_has_RC.
    - apply disp_bicat_have_pullbacks_has_RC.
    - apply disp_bicat_have_equalizers_has_RC.
  Defined.

  Theorem disp_bicat_have_limits_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_have_limits.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_have_limits_has_RC.
    - exact disp_2cells_iscontr_have_limits.
  Defined.

End CategoriesHavingFiniteLimitsAdmitRezkCompletions.

Section CategoriesWithFiniteLimitsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_limits_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_limits.
  Proof.
    repeat use make_cat_with_struct_has_RC_from_dirprod.
    - apply disp_bicat_terminal_has_RC.
    - apply disp_bicat_binproducts_has_RC.
    - apply disp_bicat_pullbacks_has_RC.
    - apply disp_bicat_equalizers_has_RC.
  Defined.

  Theorem disp_bicat_limits_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_limits.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_limits_has_RC.
    - exact disp_2cells_iscontr_limits.
  Defined.

End CategoriesWithFiniteLimitsAdmitRezkCompletions.
