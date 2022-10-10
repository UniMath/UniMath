(**************************************************************************

 Preservation of certain colimits by pullbacks

 The pullback functor always has a left biadjoint, which is given by
 composition. For that reason, pullbacks always preserve limits such as
 terminal objects, products, inserters, and equifiers. However, in general,
 the pullback functor does not have a right adjoint (this is even not the
 case in the bicategory of categories), and this pseudofunctor does not
 even preserve all colimits. If we have some additional assumptions, then
 we can show that certain colimits are preserved.
 If the bicategory has a strict biinitial (i.e., all maps into that object
 are equivalents), then the pullback pseudofunctor preserves biinitial
 objects.

 Contents
 1. Pullbacks preserve strict biinitial objects

 **************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PullbackFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Extensive.
Require Import UniMath.Bicategories.Colimits.Examples.SliceBicategoryColimits.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.

Local Open Scope cat.

(**
 1. Pullbacks preserve strict biinitial objects
 *)
Definition pullback_preserves_biinitial
           (B : bicat_with_pb)
           (HI : strict_biinitial_obj B)
           {b₁ b₂ : B}
           (f : b₁ --> b₂)
  : preserves_biinitial
      (pb_psfunctor B f).
Proof.
  pose (H := map_to_strict_biinitial_is_biinitial
               (pr2 HI)
               (pb_pr2 f (is_biinitial_1cell_property (pr12 HI) b₂))).
  use (preserves_chosen_biinitial_to_preserve_biinitial
         (_ ,, _)
         (pb_psfunctor B f)).
  - apply biinitial_in_slice.
    exact (pr1 HI ,, pr12 HI).
  - use (equiv_from_biinitial
           (is_biinitial_slice
              (pb_obj f (is_biinitial_1cell_property (pr12 HI) b₂)
               ,,
               H)
              b₁)).
    + use make_1cell_slice.
      * apply id₁.
      * cbn.
        use is_biinitial_invertible_2cell_property.
        exact H.
    + use left_adjoint_equivalence_in_slice_bicat.
      cbn.
      apply internal_adjoint_equivalence_identity.
Defined.
