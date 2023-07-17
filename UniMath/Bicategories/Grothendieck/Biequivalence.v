(************************************************************************

 The Grothendieck Construction

 The Grothendieck construction gives a biequivalence between the
 bicategory of fibrations over a fixed category `C` and the bicategory
 of indexd categories over `C`. In this file, our goal is to construct
 this particular equivalence. Except for some laws, this file collects
 constructions already given elsewhere in UniMath.

 Note: at this moment, the construction is not complete yet, because we
 need to construct a biequivalence between the bicategory of fibrations
 on `C` and the bicategory of indexed categories. We currently only have
 the pseudofunctor from fibrations to indexed categories.

 Contents
 1. From fibrations to pseudofunctors
 1.1. Preservation of the identity
 1.2. Preservation of composition
 1.3. The data
 1.4. The laws
 1.5. Pseudofunctor from fibrations to pseudofunctors
 2. From pseudofunctors to fibrations
 2.1. The action on pseudofunctors
 2.2. The action on pseudotransformations
 2.3. The action on modifications
 2.4. The identitor
 2.5. The compositor
 2.6. The data
 2.7. The laws
 2.8. The pseudofunctor from pseudofunctors to fibrations
 3. The unit
 4. The counit
 5. The biequivalence

 ************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformation.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.CartesianToIndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.NatTransToIndexed.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategoryToFibration.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctorToCartesian.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformationToTransformation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.Core.Examples.FibSlice.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PseudoFunctorsIntoCat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.PseudoTransformationIntoCat.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.ModificationIntoCat.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.Grothendieck.FibrationToPseudoFunctor.
Require Import UniMath.Bicategories.Grothendieck.PseudoFunctorToFibration.
Require Import UniMath.Bicategories.Grothendieck.Unit.
Require Import UniMath.Bicategories.Grothendieck.Counit.

Local Open Scope cat.

Section GrothendieckConstruction.
  Context (C : univalent_category).

  (**
   5. The biequivalence
   *)
  Definition psfunctor_fib_to_psfunctor_bicat_unit_counit
    : is_biequivalence_unit_counit
        (psfunctor_fib_to_psfunctor_bicat C)
        (psfunctor_psfunctor_bicat_to_fib C).
  Proof.
    refine (_ ,, _).
    - exact psfunctor_fib_to_psfunctor_unit.
    - exact psfunctor_fib_to_psfunctor_counit.
  Defined.

  Definition is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat
             (H : is_univalent_2 (fib_slice_bicat C))
    : is_biequivalence_adjoints psfunctor_fib_to_psfunctor_bicat_unit_counit.
  Proof.
    split.
    - use pointwise_adjequiv_to_adjequiv.
      + exact H.
      + intro P.
        use equiv_to_adjequiv.
        exact (psfunctor_fib_to_psfunctor_unit_equiv (pr1 P) (pr2 P)).
    - use pointwise_adjequiv_to_adjequiv.
      + use psfunctor_bicat_is_univalent_2.
        exact univalent_cat_is_univalent_2.
      + intro F.
        use pointwise_adjequiv_to_adjequiv.
        * exact univalent_cat_is_univalent_2.
        * intro x.
          use equiv_to_adjequiv.
          exact (equiv_psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x).
  Defined.

  Definition is_biequivalence_psfunctor_fib_to_psfunctor_bicat
             (H : is_univalent_2 (fib_slice_bicat C))
    : is_biequivalence (psfunctor_fib_to_psfunctor_bicat C)
    := psfunctor_psfunctor_bicat_to_fib C
       ,,
       psfunctor_fib_to_psfunctor_bicat_unit_counit
       ,,
       is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat H.

  Definition grothendieck_construction
             (H : is_univalent_2 (fib_slice_bicat C))
    : biequivalence
        (fib_slice_bicat C)
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats)
    := psfunctor_fib_to_psfunctor_bicat C
       ,,
       is_biequivalence_psfunctor_fib_to_psfunctor_bicat H.
End GrothendieckConstruction.
