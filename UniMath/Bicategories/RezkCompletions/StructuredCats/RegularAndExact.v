(*
Lifting Of Rezk Completions To Regular And Exact Categories.

In this file, we show how the Rezk completion for finitely complete categories lifts to regular and exact categories.

Contents.
1. Lifting Of Rezk Completions To Regular Categories [disp_bicat_regular_has_Rezk_completion]
2. Lifting Of Rezk Completions To Exact Categories [disp_bicat_exact_has_Rezk_completion]
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.RegularEpi.
Require Import UniMath.CategoryTheory.WeakEquivalences.Regular.
Require Import UniMath.CategoryTheory.WeakEquivalences.Exact.

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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.RegularAndExact.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteLimits.

Local Open Scope cat.

(** * 1. Lifting Of Rezk Completions To Regular Categories *)
Section RegularCategoriesAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_regular_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_regular.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_limits_has_RC _ η_weak_equiv).
    - simpl ; intros C₁ C₂ C₂_univ F F_weq [[T ?] [? [[P ?] ?]]] [[A₁ B₁] ?].
      refine (_ ,, tt).
      split.
      + exact (Rezk_completion_has_coeqs_of_kernel_pair F_weq C₂_univ P A₁).
      + exact (Rezk_completion_regular_epi_pb_stable F_weq C₂_univ B₁).
    - cbn ; intro ; intros.
      refine (tt ,, _).
      apply (weak_equiv_preserves_regular_epi (η_weak_equiv _)).
    - cbn ; intros C₁ C₂ C₃ F G H α
        ? ?
        ? ?
        ? ?
        G_weq
        ?
        [? Fre].
      refine (tt ,, _).
      exact (weak_equiv_lifts_preserves_regular_epi C₂ C₃ α G_weq Fre).
  Defined.

  Theorem disp_bicat_regular_has_Rezk_completion
    : cat_with_structure_has_RezkCompletion disp_bicat_regular.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_regular_has_RC.
    - apply disp_2cells_iscontr_regular.
  Defined.

End RegularCategoriesAdmitRezkCompletions.

(** * 2. Lifting Of Rezk Completions To Exact Categories *)
Section ExactCategoriesAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_exact_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_exact.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_regular_has_RC _ η_weak_equiv).
    - simpl ; intros C₁ C₂ C₂_univ F F_weq [[? [? [[P ?] C]]] R] H.
      exact (weak_equiv_effective_internal_eqrel F_weq C₂_univ P H).
    - cbn ; intro ; intros ; exact tt.
    - intro ; intros ; exact tt.
  Defined.

  Theorem disp_bicat_exact_has_Rezk_completion
    : cat_with_structure_has_RezkCompletion disp_bicat_exact.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_exact_has_RC.
    - apply disp_2cells_iscontr_exact.
  Defined.

End ExactCategoriesAdmitRezkCompletions.
