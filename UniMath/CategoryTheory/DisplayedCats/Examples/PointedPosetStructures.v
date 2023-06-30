(*****************************************************************

 Pointed posets

 In this file, we define the category of pointed posets and
 monotone functions (not necessarily strict) as a category of
 structured sets. We also show that it is a cartesian structure.

 Note: since we don't require that the morphisms are strict
 functions (i.e., preserve the bottom element), this category is
 not complete and cocomplete. It is also not cartesian closed.

 Contents
 1. Structures of pointed posets
 2. Cartesian structure of posets

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.

(**
 1. Structures of pointed posets
 *)
Definition struct_pointed_poset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, pointed_PartialOrder X).
  - exact (λ X Y PX PY f, is_monotone PX PY f).
Defined.

Definition struct_pointed_poset_laws
  : hset_struct_laws struct_pointed_poset_data.
Proof.
  split5.
  - intro X.
    use isaset_total2.
    + apply isaset_PartialOrder.
    + intro PX.
      apply isasetaprop.
      apply isaprop_bottom_element.
  - intros X Y PX PY f.
    apply isaprop_is_monotone.
  - intros X PX.
    apply idfun_is_monotone.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_monotone Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_pointed_PartialOrder_monotone p q).
Qed.

Definition struct_pointed_poset
  : hset_struct
  := struct_pointed_poset_data ,, struct_pointed_poset_laws.

(**
 2. Cartesian structure of posets
 *)
Definition cartesian_struct_pointed_poset_data
  : hset_cartesian_struct_data
  := struct_pointed_poset
     ,,
     unit_pointed_PartialOrder
     ,,
     λ X Y PX PY, prod_pointed_PartialOrder PX PY.

Definition cartesian_struct_pointed_poset_laws
  : hset_cartesian_struct_laws cartesian_struct_pointed_poset_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X PX ; cbn in *.
    intros x y p.
    exact tt.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr1_is_monotone.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr2_is_monotone.
  - intros W X Y PW PY PZ f g Pf Pg ; cbn in *.
    exact (prodtofun_is_monotone Pf Pg).
Qed.

Definition cartesian_struct_pointed_poset
  : hset_cartesian_struct
  := cartesian_struct_pointed_poset_data
     ,,
     cartesian_struct_pointed_poset_laws.
