(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PlainBicat.Bicat.
Require Import UniMath.CategoryTheory.PlainBicat.DispBicat.
Require Import UniMath.CategoryTheory.PlainBicat.BicatOfCats.

Open Scope cat.
Open Scope mor_disp_scope.

Notation "f' ==>[ x ] g'" := (disp_cells x f' g') (at level 60).


Definition bar : disp_cat_data bicat_of_cats.
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

Definition foo : disp_prebicat_1_id_comp_cells bicat_of_cats.
Proof.
  exists bar.
  cbn. intros C C' F F' a D D' G G'. cbn in *.
  apply (disp_nat_trans a G G').
Defined.

Definition disp_prebicat_of_disp_cats_data : disp_prebicat_data bicat_of_cats.
Proof.
  use tpair.


Definition DispBicatOfDispCats : disp_prebicat bicat_of_cats.
Proof.
  use tpair.
  -