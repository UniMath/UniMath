(*
In this file, we show how the Rezk completion of a categories has a suitable binary products (in terms of preservation) if the original category has binary products.
Hence, categories with binary products admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithBinProductsHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with binary products (up to propositional truncation).
2. BicatOfCategoriesWithChosenBinProductsHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with chosen binary products.
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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Local Open Scope cat.

Section CategoriesWithBinProductsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Definition cat_with_binproducts_has_RezkCompletion
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_have_binproducts
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_binproducts)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
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

  Definition cat_with_chosen_binproducts_has_RezkCompletion
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_chosen_binproducts
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_binproducts)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
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

End CategoriesWithBinProductsAdmitRezkCompletions.
