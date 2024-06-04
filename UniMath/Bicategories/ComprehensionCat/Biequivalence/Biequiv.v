(*******************************************************************************************

 The biequivalence between categories with finite limits and comprehension categories

 In this file, we conclude the construction of the biequivalence between the bicategory of
 univalent categories with finite limits and the bicategory of DFL comprehension categories.
 This corresponds to the first part of Theorem 6.1 in the paper "The biequivalence of locally
 cartesian closed categories and Martin-Löf type theories" by Clairambault and Dybjer.

 In the file on DFL comprehension categories, we already mentioned some differences between
 our construction and theirs. However, these only concered the fact that Clairambault and Dybjer
 considered categories with families, whereas we consider comprehension categories, and the fact
 that we consider univalent categories. There is one more difference to notice. Clairambault
 and Dybjer construct the inverse pseudonatural transformations and the modifications explicitly,
 whereas we use the fact that a pseudotransformation is an adjoint equivalence if it is a
 pointwise adjoint equivalence. This simplifies the construction, because we only have to
 construct two pseudotransformations and we don't have to construct any invertible modification.

 References
 - "The biequivalence of locally cartesian closed categories and Martin-Löf type theories" by
   Clairambault and Dybjer

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.

Local Open Scope cat.

Definition finlim_dfl_comp_cat_biequivalence_unit_counit
  : is_biequivalence_unit_counit
      finlim_to_dfl_comp_cat_psfunctor
      dfl_comp_cat_to_finlim_psfunctor
  := finlim_dfl_comp_cat_unit
     ,,
     finlim_dfl_comp_cat_counit_inv.

Definition finlim_dfl_comp_cat_biequivalence_adjoints
  : is_biequivalence_adjoints finlim_dfl_comp_cat_biequivalence_unit_counit.
Proof.
  split.
  - exact finlim_dfl_comp_cat_unit_left_adjoint_equivalence.
  - apply inv_left_adjoint_equivalence.
Defined.

Definition is_biequivalence_finlim_to_dfl_comp_cat_psfunctor
  : is_biequivalence finlim_to_dfl_comp_cat_psfunctor
  := dfl_comp_cat_to_finlim_psfunctor
     ,,
     finlim_dfl_comp_cat_biequivalence_unit_counit
     ,,
     finlim_dfl_comp_cat_biequivalence_adjoints.

Definition finlim_biequiv_dfl_comp_cat_psfunctor
  : biequivalence
      bicat_of_univ_cat_with_finlim
      bicat_of_dfl_full_comp_cat
  := finlim_to_dfl_comp_cat_psfunctor
     ,,
     is_biequivalence_finlim_to_dfl_comp_cat_psfunctor.
