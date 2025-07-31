(**

 Categories with universes versus comprehension categories with universes

 Clairambault and Dybjer established a biequivalence between the bicategory of democratic
 categories with families that support ∑-types and extensional identity types, and the
 bicategory of finitely complete categories. This biequivalence can be established in the
 univalent setting as well: specifically, the bicategory of univalent democratic full
 comprehension categories that support unit types, product types, ∑-types, and extensional
 identity types is equivalent to the bicategory of univalent categories with finite limits.
 One can extend this biequivalence in various ways by including more and more type formers.

 In this file, we extend the aforementioned biequivalence with universe types. Specifically,
 we show that the bicategory of univalent categories with finite limits and a universe type
 is biequivalence to the bicategory of univalent democratic full comprehension categories
 that support unit types, product types, ∑-types, extensional identity types, and a universe
 type. These universes are in Tarski-style, and they are represented in a way that is close
 to what one would expect from a type theoretic perspective. Specifically, all of the rules
 regarding Tarski-style universes are postulated.

 The necessary ingredients of the desired biequivalences are constructed in other files, and
 here we only put them to obtain a biequivalence.

 References
 - "The biequivalence of locally cartesian closed categories and Martin-Löf type theories"
   by Clairambault and Dybjer
 - "The internal languages of univalent categories" by Van der Weide


                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudoNaturalAdjequiv.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.UnitForUniv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Definition finlim_dfl_comp_cat_biequivalence_unit_counit_universe
  : is_disp_biequivalence_unit_counit
      _ _
      finlim_dfl_comp_cat_biequivalence_unit_counit
      finlim_to_dfl_comp_cat_disp_psfunctor_universe
      dfl_comp_cat_to_finlim_disp_psfunctor_universe.
Proof.
  use make_disp_biequiv_unit_counit_pointwise_adjequiv_alt.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
  - exact finlim_dfl_comp_cat_biequivalence_adjoints.
  - exact disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact dfl_comp_cat_to_finlim_disp_psfunctor_unit.
  - exact dfl_comp_cat_to_finlim_disp_psfunctor_counit.
  - intros C u.
    apply disp_left_adjoint_equivalence_comp_cat_universe.
Defined.

Definition finlim_biequiv_dfl_comp_cat_psfunctor_universe
  : disp_is_biequivalence_data
      _
      _
      finlim_dfl_comp_cat_biequivalence_adjoints
      finlim_dfl_comp_cat_biequivalence_unit_counit_universe.
Proof.
  use (make_disp_biequiv_pointwise_adjequiv_alt _ _).
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - exact disp_2cells_isaprop_disp_bicat_finlim_universe.
  - exact disp_locally_groupoid_disp_bicat_finlim_universe.
  - intros C u.
    apply disp_left_adjoint_equivalence_finlim_universe.
Defined.
