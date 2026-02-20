(**
In this file, we conclude that the Rezk completion for categories lifts to finitely cocomplete categories.

Contents:
1. [CategoriesWithFiniteColimitsAdmitRezkCompletions] proves the existence of a displayed universal arrow for the inclusion of univalent finitely cocomplete categories into all finitely cocomplete categories.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Initial.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Initial.
Require Import UniMath.CategoryTheory.WeakEquivalences.Coequalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Bincoproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinCoproducts.

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteColimits.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.

Local Open Scope cat.

(** * 1. Rezk completion for finitely cocomplete categories *)
Section CategoriesWithFiniteColimitsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_initial_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_initial.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [T1 _].
      exact (make_Initial _ (weak_equiv_preserves_initial _ Fw _ (pr2 T1)) ,, tt).
    - intros C [T1 ?].
      refine (tt ,, _).
      use weak_equiv_preserves_initial.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fpinit].
      exists tt.
      exact (weak_equiv_lifts_preserves_initial α Gw Fpinit).
  Defined.

  Corollary disp_bicat_initial_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_initial.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_initial_has_RC).
    exact disp_2cells_iscontr_initial.
  Defined.

  Lemma disp_bicat_bincoproducts_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_bincoproducts.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [P1 _].
      exact (weak_equiv_creates_bincoproducts Fw P1 C2_univ ,, tt).
    - intros C [P1 ?].
      refine (tt ,, _).
      use weak_equiv_preserves_bincoproducts.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fp].
      exists tt.
      exact (weak_equiv_lifts_preserves_bincoproducts C2 C3 α Gw Fp).
  Defined.

  Corollary disp_bicat_bincoproducts_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_bincoproducts.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_bincoproducts_has_RC).
    exact disp_2cells_iscontr_bincoproducts.
  Defined.

  Lemma disp_bicat_coequalizers_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_coequalizers.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [P1 _].
      exact (weak_equiv_creates_coequalizers Fw C2_univ P1 ,, tt).
    - intros C [P1 ?].
      refine (tt ,, _).
      use weak_equiv_preserves_coequalizers.
      apply η_weak_equiv.
    - simpl ; intros C1 C2 C3 F G H α [T1 _] [T2 _] [T3 _] Gw.
      intros [t Fp].
      exists tt.
      exact (weak_equiv_lifts_preserves_coequalizers C2 C3 α Gw Fp).
  Defined.

  Corollary disp_bicat_coequalizers_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_coequalizers.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_coequalizers_has_RC).
    exact disp_2cells_iscontr_coequalizers.
  Defined.

  Lemma disp_bicat_colimits_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_colimits.
  Proof.
    repeat use make_cat_with_struct_has_RC_from_dirprod.
    - apply disp_bicat_initial_has_RC.
    - apply disp_bicat_bincoproducts_has_RC.
    - apply disp_bicat_coequalizers_has_RC.
  Defined.

  Theorem disp_bicat_colimits_has_RezkCompletion
    : cat_with_structure_has_RezkCompletion disp_bicat_colimits.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_colimits_has_RC.
    - exact disp_2cells_iscontr_colimits.
  Defined.

End CategoriesWithFiniteColimitsAdmitRezkCompletions.
