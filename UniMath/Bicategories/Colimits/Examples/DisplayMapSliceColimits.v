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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.DisplayMapBicat.

Local Open Scope cat.

Section ArrowSubbicatInitial.
  Context {B : bicat}
          (I : biinitial_obj B)
          (D : arrow_subbicat B)
          (b : B)
          (HD : arrow_subbicat_biinitial I D).

  Definition disp_map_slice_biinitial_obj
    : disp_map_slice_bicat D b.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (pr1 I).
    - exact (is_biinitial_1cell_property (pr2 I) b).
    - exact (pr1 HD b).
  Defined.

  Definition disp_map_slice_biinitial_1cell_property
    : biinitial_1cell_property disp_map_slice_biinitial_obj.
  Proof.
    intros h.
    simple refine (_ ,, _ ,, _).
    - exact (is_biinitial_1cell_property (pr2 I) (pr1 h)).
    - exact (pr2 HD _ _ (pr12 h)).
    - use make_invertible_2cell ; cbn.
      + apply (is_biinitial_2cell_property (pr2 I)).
      + use make_is_invertible_2cell.
        * apply (is_biinitial_2cell_property (pr2 I)).
        * apply (is_biinitial_eq_property (pr2 I)).
        * apply (is_biinitial_eq_property (pr2 I)).
  Defined.

  Definition disp_map_slice_biinitial_2cell_property
             (h : disp_map_slice_bicat D b)
    : biinitial_2cell_property disp_map_slice_biinitial_obj h.
  Proof.
    intros α β.
    simple refine (_ ,, _).
    - apply (is_biinitial_2cell_property (pr2 I)).
    - apply (is_biinitial_eq_property (pr2 I)).
  Defined.

  Definition disp_map_slice_biinitial_eq_property
             (h : disp_map_slice_bicat D b)
    : biinitial_eq_property disp_map_slice_biinitial_obj h.
  Proof.
    intros α β p q.
    use eq_2cell_disp_map_slice.
    apply (is_biinitial_eq_property (pr2 I)).
  Defined.

  Definition disp_map_slice_biinitial
    : biinitial_obj (disp_map_slice_bicat D b).
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_biinitial_obj.
    - use make_is_biinitial.
      + exact disp_map_slice_biinitial_1cell_property.
      + exact disp_map_slice_biinitial_2cell_property.
      + exact disp_map_slice_biinitial_eq_property.
  Defined.
End ArrowSubbicatInitial.
