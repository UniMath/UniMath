(*
In this file, we show how the Rezk completion of a categories has a suitable binary products (in terms of preservation) if the original category has binary products.
Hence, categories with binary products admit a Rezk completion.

Contents:
1. [BicatOfCategoriesWithBinProductsHasRezkCompletion]
   A construction of the Rezk completion of categories (merely) having binary products.
2. [BicatOfCategoriesWithChosenBinProductsHasRezkCompletion]
   A construction of the Rezk completion of categories equipped with chosen binary products.
3. [CategoriesWithChosenTerminalAndPreservationIsCreationHasRezkCompletions]
   A construction of the Rezk completion for categories equipped with a chosen binary products.
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

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinProducts.

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
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.BinProducts.

Local Open Scope cat.

Section CategoriesWithBinProductsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_have_binproducts_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_have_binproducts.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw BP₁.
      exact (weak_equiv_into_univ_creates_hasbinproducts C2_univ Fw (pr1 BP₁) ,, tt).
    - intros C BP.
      refine (tt ,, _).
      apply weak_equiv_preserves_binproducts.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α C1_prod C2_prod C3_prod Gw.
      intros [t Fprod].
      exists tt.
      exact (weak_equiv_lifts_preserves_binproducts C2 C3 α Gw Fprod).
  Defined.

  Corollary disp_bicat_have_binproducts_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_have_binproducts.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_have_binproducts_has_RC).
    exact disp_2cells_iscontr_have_binproducts.
  Defined.

End CategoriesWithBinProductsAdmitRezkCompletions.

Section CategoriesWithChosenBinProductsAndPreservationUpToEqualityHasRezkCompletions.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Definition disp_bicat_chosen_binproducts_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_chosen_binproducts.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw C1_prod.
      exact (weak_equiv_into_univ_creates_binproducts C2_univ Fw (pr1 C1_prod) ,, tt).
    - intros C C1_prod.
      refine (tt ,, _).
      use weak_equiv_preserves_binproducts_eq.
      + apply η_weak_equiv.
      + exact (pr2 (pr1 LUR C)).
    - intros C1 C2 C3 F G H α C1_prod C2_prod C3_prod Gw.
      intros [t Fprod].
      exists tt.
      exact (weak_equiv_lifts_preserves_chosen_binproducts_eq C2 C3 α (pr1 C1_prod) (pr1 C2_prod) (pr1 C3_prod) Gw Fprod).
  Defined.

  Corollary disp_bicat_chosen_binproducts_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_chosen_binproducts.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_chosen_binproducts_has_RC).
    exact disp_2cells_iscontr_chosen_binproducts.
  Defined.

End CategoriesWithChosenBinProductsAndPreservationUpToEqualityHasRezkCompletions.

Section CategoriesWithChosenBinProductsAndPreservationIsCreationHasRezkCompletions.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Lemma disp_bicat_binproducts_has_RC
    : cat_with_struct_has_RC η_weak_equiv disp_bicat_binproducts.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F Fw [BP1 ?].
      exact (weak_equiv_into_univ_creates_binproducts C2_univ Fw BP1 ,, tt).
    - intros C [BP1 ?].
      refine (tt ,, _).
      apply weak_equiv_preserves_binproducts.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α C1_prod C2_prod C3_prod Gw.
      intros [t Fprod].
      exists tt.
      exact (weak_equiv_lifts_preserves_binproducts C2 C3 α Gw Fprod).
  Defined.

  Corollary disp_bicat_binproducts_has_Rezk_completions
    : cat_with_structure_has_RezkCompletion disp_bicat_binproducts.
  Proof.
    apply (make_RezkCompletion_from_locally_contractible _ _ disp_bicat_binproducts_has_RC).
    exact disp_2cells_iscontr_binproducts.
  Defined.

End CategoriesWithChosenBinProductsAndPreservationIsCreationHasRezkCompletions.
