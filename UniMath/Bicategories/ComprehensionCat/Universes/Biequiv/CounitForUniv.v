(**

 Categories with universes versus comprehension categories with universes: the counit

 Our goal is to establish a biequivalence between the bicategories of univalent categories
 with finite limits and a universe type and the bicategory of univalent full DFL comprehension
 categories that have a universe.

 The mathematical development of the counit is rather straightforward. However, there are
 some technical issues, namely keeping the memory consumption and the running time acceptable.
 Tricks to decrease the running time are documented in the file, and the development of the
 pointwise morphism and the naturality squares are split up into separate files. In this file,
 we construct the displayed pseudotransformation.

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUnivMor.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUnivNat.

Local Open Scope cat.
Local Open Scope comp_cat.

Definition dfl_comp_cat_to_finlim_disp_psfunctor_counit
  : disp_pstrans
      (disp_pseudo_id disp_bicat_dfl_full_comp_cat_with_univ)
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_universe
         finlim_to_dfl_comp_cat_disp_psfunctor_universe)
      finlim_dfl_comp_cat_counit.
  use make_disp_pstrans.
  - exact disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ.
  - intros C u.
    simple refine (_ ,, _).
    + exact (finlim_dfl_comp_cat_counit_ob (pr1 u)).
    + exact (finlim_dfl_comp_cat_counit_preserves_univ_type (pr1 u) (pr2 u)).
  - intros C₁ C₂ F u₁ u₂ Fu.
    simple refine (_ ,, _).
    + exact (finlim_dfl_comp_cat_counit_natural_ob_lem F (pr1 Fu)).
    + exact (finlim_dfl_comp_cat_counit_natural_preserves_univ_type F (pr1 Fu) (pr2 Fu)).
Defined.
