(******************************************************************************************

 The internal language of toposes

 In other files, we gave several extensions of the biequivalence between categories with
 finite limits and full DFL comprehension categories. Now we put these extensions together
 in order to obtain internal language theorems for several classes of toposes.

 We look at 3 classes of toposes. The first one is given by pretoposes. A pretopos is a
 category that is extensive and exact. This can be expressed via a local property, and
 from that we directly obtain the biequivalence. The second class is given by ∏-pretoposes.
 These are pretoposes that are locally Cartesian closed, so we combine the biequivalence for
 pi-types together with the biequivalence for being a pretopos. More precisely, we take the
 product of these two displayed biequivalence. The third class is given by elementary toposes.
 Note that there are many equivalent ways to define elementary toposes. The most common one
 is as a cartesian closed category with finite limits and a subobject classifier. However,
 here use a definition that contains more redundancy, but that results in a more expressive
 internal language. More precisely, here we define elementary toposes as categories that
 are exact, extensive, locally cartesian closed, and that have finite limits and a subobject
 classifier. Note that this definition is equivalent to the other one.

 Contents
 1. The internal language of pretoposes
 2. The internal language of ∏-pretoposes
 3. The internal language of elementary pretoposes

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.ProductDispBiequiv.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SubobjectTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.CatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.SubobjectClassifier.

(** * 1. The internal language of pretoposes *)
Definition bicat_of_univ_pretoposes
  : bicat
  := total_bicat
       (disp_bicat_of_univ_cat_with_cat_property pretoposes_local_property).

Definition univ_pretoposes_language
  : bicat
  := total_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat pretoposes_local_property).

Definition lang_univ_pretopos
  : psfunctor
      bicat_of_univ_pretoposes
      univ_pretoposes_language
  := total_psfunctor
       _ _ _
       (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property pretoposes_local_property).

Definition internal_language_univ_pretopos
  : is_biequivalence lang_univ_pretopos
  := total_is_biequivalence
       _ _ _
       (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
          pretoposes_local_property).

(** * 2. The internal language of ∏-pretoposes *)
Definition disp_bicat_of_univ_pretoposes
  : disp_bicat bicat_of_univ_cat_with_finlim
  := disp_dirprod_bicat
       (disp_bicat_of_univ_cat_with_cat_property pretoposes_local_property)
       disp_bicat_univ_lccc.

Definition bicat_of_univ_pi_pretoposes
  : bicat
  := total_bicat disp_bicat_of_univ_pretoposes.

Definition disp_bicat_univ_pi_pretoposes_language
  : disp_bicat bicat_of_dfl_full_comp_cat
  := disp_dirprod_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat pretoposes_local_property)
       disp_bicat_of_pi_type_dfl_full_comp_cat.

Definition univ_pi_pretoposes_language
  : bicat
  := total_bicat disp_bicat_univ_pi_pretoposes_language.

Definition disp_psfunctor_lang_univ_pi_pretopos
  : disp_psfunctor
      disp_bicat_of_univ_pretoposes
      disp_bicat_univ_pi_pretoposes_language
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  refine (prod_disp_psfunctor
            _ _ _ _
            (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
               pretoposes_local_property)
            finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types).
  - apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition lang_univ_pi_pretopos
  : psfunctor
      bicat_of_univ_pi_pretoposes
      univ_pi_pretoposes_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_univ_pi_pretopos.

Definition internal_language_univ_pi_pretopos
  : is_biequivalence lang_univ_pi_pretopos.
Proof.
  refine (total_is_biequivalence
            _ _ _
            (prod_disp_is_biequivalence_data
               _ _ _ _
               _ _ _ _
               _ _ _ _
               _ _ _ _
               (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
                  pretoposes_local_property)
               finlim_biequiv_dfl_comp_cat_psfunctor_pi_types)).
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
Defined.

(** * 3. The internal language of elementary pretoposes *)
Definition disp_bicat_of_univ_elementary_toposes
  : disp_bicat bicat_of_univ_cat_with_finlim
  := disp_dirprod_bicat
       disp_bicat_of_univ_pretoposes
       disp_bicat_finlim_subobject_classifier.

Definition bicat_of_univ_elementary_toposes
  : bicat
  := total_bicat disp_bicat_of_univ_elementary_toposes.

Definition disp_bicat_univ_elementary_toposes_language
  : disp_bicat bicat_of_dfl_full_comp_cat
  := disp_dirprod_bicat
       disp_bicat_univ_pi_pretoposes_language
       disp_bicat_of_subobject_classifier_type.

Definition univ_elementary_toposes_language
  : bicat
  := total_bicat disp_bicat_univ_elementary_toposes_language.

Definition disp_psfunctor_lang_elementary_topos
  : disp_psfunctor
      disp_bicat_of_univ_elementary_toposes
      disp_bicat_univ_elementary_toposes_language
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  refine (prod_disp_psfunctor
            _ _ _ _
            disp_psfunctor_lang_univ_pi_pretopos
            finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier).
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
    + exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - use disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_2cells_isaprop_disp_bicat_of_subobject_classifier_type.
  - apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
Defined.

Definition lang_univ_elementary_topos
  : psfunctor
      bicat_of_univ_elementary_toposes
      univ_elementary_toposes_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_elementary_topos.

Definition internal_language_univ_elementary_topos
  : is_biequivalence lang_univ_elementary_topos.
Proof.
  refine (total_is_biequivalence
            _ _ _
            (prod_disp_is_biequivalence_data
               _ _ _ _
               _ _ _ _
               _ _ _ _
               _ _ _ _
               (prod_disp_is_biequivalence_data
                  _ _ _ _
                  _ _ _ _
                  _ _ _ _
                  _ _ _ _
                  (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
                     pretoposes_local_property)
                  finlim_biequiv_dfl_comp_cat_psfunctor_pi_types)
               finlim_biequiv_dfl_comp_cat_psfunctor_subobject_classifier)).
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
    + exact disp_2cells_isaprop_univ_lccc.
  - use disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    + exact disp_locally_groupoid_univ_lccc.
  - apply disp_2cells_isaprop_finlim_subobject_classifier.
  - apply disp_locally_groupoid_finlim_subobject_classifier.
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
Defined.
