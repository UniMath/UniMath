(*
  Lifting Of Rezk Completions To Extensive Categories.

  In this file, we show how the Rezk completion for categories with binary coproducts lifts to extensive categories.

  Contents.
  1. Lifting Of Rezk Completions To Regular Categories [disp_bicat_extensive_has_Rezk_completion]

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.RegularEpi.
Require Import UniMath.CategoryTheory.WeakEquivalences.Extensivity.

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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Extensive.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteColimits.

Local Open Scope cat.

(** * 1. Lifting Of Rezk Completions To Extensive Categories *)
Section ExtensiveCategoriesAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_extensive_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_extensive_cats.
  Proof.
    use make_cat_with_struct_has_RC_from_sigma ; cbn.
    - exact (disp_bicat_bincoproducts_has_RC LUR η_weak_equiv).
    - intros C₁ C₂ C₂_univ F F_weq [c ?] E₁.
      apply (weak_equiv_preserves_extensivity C₂_univ F_weq E₁).
    - intro ; intros ; exact tt.
    - intro ; intros ; exact tt.
  Defined.

  Theorem disp_bicat_extensive_has_Rezk_completion
    : cat_with_structure_has_RezkCompletion disp_bicat_extensive_cats.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible η_weak_equiv).
    - exact disp_bicat_extensive_has_RC.
    - apply disp_2cells_iscontr_extensive_cats.
  Defined.

End ExtensiveCategoriesAdmitRezkCompletions.
