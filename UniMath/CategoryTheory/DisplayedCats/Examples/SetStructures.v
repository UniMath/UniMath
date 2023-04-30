(*****************************************************************

 Set structures

 A simple example of a structure of sets, would be the trivial
 structure. Structures above sets and morphisms would be be
 inhabitants of the unit type

 Contents
 1. The trivial structure
 2. The trivial structure is cartesian
 3. The trivial structure is cartesian closed
 4. Some limits and colimits for trivial structures

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.

(**
 1. The trivial structure
 *)
Definition struct_plain_hset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, unit).
  - exact (λ X Y x y f, unit).
Defined.

Definition struct_plain_hset_laws
  : hset_struct_laws struct_plain_hset_data.
Proof.
  repeat split.
  - intro X.
    apply isasetunit.
  - intros X Y px py f.
    apply isapropunit.
  - intros X px py f g.
    apply isapropunit.
Qed.

Definition struct_plain_hset
  : hset_struct
  := struct_plain_hset_data ,, struct_plain_hset_laws.

(**
 2. The trivial structure is cartesian
 *)
Definition cartesian_struct_plain_hset_data
  : hset_cartesian_struct_data
  := struct_plain_hset ,, tt ,, λ _ _ _ _, tt.

Definition cartesian_struct_plain_hset_laws
  : hset_cartesian_struct_laws cartesian_struct_plain_hset_data.
Proof.
  repeat split.
Qed.

Definition cartesian_struct_plain_hset
  : hset_cartesian_struct
  := cartesian_struct_plain_hset_data ,, cartesian_struct_plain_hset_laws.

(**
 3. The trivial structure is cartesian closed
 *)
Definition cartesian_closed_struct_plain_hset_data
  : hset_cartesian_closed_struct_data.
Proof.
  simple refine (cartesian_struct_plain_hset ,, _ ,, _).
  - exact (λ _ _ _ _ _, tt).
  - exact (λ _ _ _ _, tt).
Defined.

Definition cartesian_closed_struct_plain_hset_laws
  : closed_under_fun_laws cartesian_closed_struct_plain_hset_data.
Proof.
  repeat split.
Qed.

Definition cartesian_closed_struct_plain_hset
  : hset_cartesian_closed_struct
  := cartesian_closed_struct_plain_hset_data
     ,,
     cartesian_closed_struct_plain_hset_laws.

(**
 4. Some limits and colimits for trivial structures
 *)
Definition equalizers_struct_plain_hset
  : hset_equalizer_struct struct_plain_hset.
Proof.
  refine ((λ _ _ _ _ _ _ _ _, tt) ,, _).
  abstract (repeat split).
Defined.

Definition coequalizers_struct_plain_hset
  : hset_coequalizer_struct struct_plain_hset.
Proof.
  refine ((λ _ _ _ _ _ _ _ _, tt) ,, _).
  abstract (repeat split).
Defined.

Definition type_products_struct_plain_hset
           (I : UU)
  : hset_struct_type_prod struct_plain_hset I.
Proof.
  simple refine ((λ _ _, tt) ,, _).
  abstract (repeat split).
Defined.
