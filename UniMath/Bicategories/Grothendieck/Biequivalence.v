(************************************************************************

 The Grothendieck Construction: the biequivalence

 The Grothendieck construction gives a biequivalence between the
 bicategory of fibrations over a fixed category `C` and the bicategory
 of indexed categories over `C`. To construct this biequivalence, we
 need to construct the following:
 1. A pseudofunctor from the bicategory of fibrations to the bicategory
    of pseudofunctors
 2. A pseudofunctor from the bicategory of pseudofunctors to the
    bicategory of fibrations
 3. The unit and a proof that it is a pointwise adjoint equivalence
 4. The counit and a proof that it is a pointwise adjoint equivalence

 In this file, we collect all statements together so that we obtain the
 desired biequivalence.

 In the proof, we make use of the fact that a pseudotransformation is an
 adjoint equivalence if it is a pointwise adjoint equivalence. The current
 proof of that in UniMath requires the univalence of the codomain, so that
 one can use induction on adjoint equivalences.

 Contents
 1. Collecting the data of the biequivalence
 2. Collecting that the unit and counit are adjoint equivalences
 3. The Grothendieck construction as biequivalence

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
   1. Collecting the data of the biequivalence
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

  (**
   2. Collecting that the unit and counit are adjoint equivalences
   *)
  Definition is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat
    : is_biequivalence_adjoints psfunctor_fib_to_psfunctor_bicat_unit_counit.
  Proof.
    split.
    - use pointwise_adjequiv_to_adjequiv.
      + exact (is_univalent_2_fib_slice_bicat C).
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

  (**
   3. The Grothendieck construction as biequivalence
   *)
  Definition is_biequivalence_psfunctor_fib_to_psfunctor_bicat
    : is_biequivalence (psfunctor_fib_to_psfunctor_bicat C)
    := psfunctor_psfunctor_bicat_to_fib C
       ,,
       psfunctor_fib_to_psfunctor_bicat_unit_counit
       ,,
       is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat.

  Definition grothendieck_construction
    : biequivalence
        (fib_slice_bicat C)
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats)
    := psfunctor_fib_to_psfunctor_bicat C
       ,,
       is_biequivalence_psfunctor_fib_to_psfunctor_bicat.
End GrothendieckConstruction.
