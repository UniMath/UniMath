(*********************************************************************************

 Colimits in slice bicategory

 Contents:
 1. Initial object

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Colimits.Initial.

Local Open Scope cat.

Section InitialSlice.
  Context {B : bicat}
          (I : biinitial_obj B)
          (b : B).

  Let κ : slice_bicat b
    := pr1 I ,, is_biinitial_1cell_property (pr2 I) b.

  Definition biinitial_1cell_property_slice
    : biinitial_1cell_property κ.
  Proof.
    intros f.
    refine (is_biinitial_1cell_property (pr2 I) _ ,, _) ; cbn.
    apply (is_biinitial_invertible_2cell_property (pr2 I)).
  Defined.

  Definition biinitial_2cell_property_slice
             (f : slice_bicat b)
    : biinitial_2cell_property κ f.
  Proof.
    intros g₁ g₂.
    simple refine (_ ,, _).
    - apply (is_biinitial_2cell_property (pr2 I)).
    - apply (is_biinitial_eq_property (pr2 I)).
  Defined.

  Definition biinitial_eq_property_slice
             (f : slice_bicat b)
    : biinitial_eq_property κ f.
  Proof.
    intros g₁ g₂ α β.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    apply (is_biinitial_eq_property (pr2 I)).
  Qed.

  Definition is_biinitial_slice
    : is_biinitial κ.
  Proof.
    refine (_ ,, _).
    - exact biinitial_1cell_property_slice.
    - intro f.
      split.
      + exact (biinitial_2cell_property_slice f).
      + exact (biinitial_eq_property_slice f).
  Defined.

  Definition biinitial_in_slice
    : biinitial_obj (slice_bicat b)
    := κ ,, is_biinitial_slice.
End InitialSlice.
