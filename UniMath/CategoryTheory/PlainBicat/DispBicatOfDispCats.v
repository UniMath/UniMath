(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PlainBicat.Bicat.
Require Import UniMath.CategoryTheory.PlainBicat.DispBicat.
Require Import UniMath.CategoryTheory.PlainBicat.BicatOfCats.

Open Scope cat.
Open Scope mor_disp_scope.

Notation "f' ==>[ x ] g'" := (disp_cells x f' g') (at level 60).


Definition disp_prebicat_of_disp_cats_cat_data : disp_cat_data bicat_of_cats.
Proof.
  use tpair.
  - use tpair.
    + exact (λ C : category, disp_cat C).
    + cbn. intros C C' D D' F. exact (disp_functor F D D').
  - use tpair; cbn.
    + intros C D.
      apply disp_functor_identity.
    + cbn. intros C C' C'' F F' D D' D'' G G'.
      apply (disp_functor_composite G G').
Defined.

Definition disp_prebicat_of_disp_cats_1_id_comp_cells
  : disp_prebicat_1_id_comp_cells bicat_of_cats.
Proof.
  exists disp_prebicat_of_disp_cats_cat_data.
  cbn. intros C C' F F' a D D' G G'. cbn in *.
  apply (disp_nat_trans a G G').
Defined.

Definition disp_prebicat_of_disp_cats_data : disp_prebicat_data bicat_of_cats.
Proof.
  exists disp_prebicat_of_disp_cats_1_id_comp_cells.
  repeat split; cbn; intros until 0; try refine (disp_nat_trans_id _).
  - intros rr ss. apply (disp_nat_trans_comp rr ss).
  - intros rr.
    use tpair.
    + cbn. red. intros A AA.
      cbn.
      apply (rr).
    + red. cbn. intros A B F AA BB FF.
      pose (RR := @disp_nat_trans_ax _ _ _ _ _ _ _ _ _ rr).
      etrans.
      * apply RR.
      * apply maponpaths_2. apply uip. apply homset_property.
  - intros rr.
    use tpair.
    + cbn. red. intros A AA.
      cbn.
      apply disp_functor_on_morphisms.
      apply rr.
    + red. cbn. intros A B F AA BB FF.
      etrans.
      apply pathsinv0.
      apply disp_functor_comp_var.
      etrans.
      Focus 2.
      apply maponpaths.
      apply disp_functor_comp_var.
      apply pathsinv0.
      etrans.
      apply transport_f_f.
      etrans.
      * apply maponpaths.
        apply maponpaths.
        pose (RR := @disp_nat_trans_ax_var _ _ _ _ _ _ _ _ _ rr).
        apply RR.
      * etrans.
        apply maponpaths.
        apply disp_functor_transportf.
        etrans.
        apply transport_f_f.
        apply maponpaths_2. apply uip. apply homset_property.
Defined.

Definition DispBicatOfDispCats : disp_prebicat bicat_of_cats.
Proof.
  use tpair.
  -