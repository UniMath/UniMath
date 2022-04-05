(**
 Morphisms in op2 bicat

 Contents
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 3. Conservative 1-cells
 4. Discrete 1-cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

(**
 1. Faithful 1-cells
 *)
Definition faithful_op2_bicat
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : faithful_1cell f)
  : @faithful_1cell (op2_bicat B) _ _ f.
Proof.
  intros z g₁ g₂ α β p.
  apply Hf.
  exact p.
Defined.

(**
 2. Fully faithful 1-cells
 *)
Definition fully_faithful_op2_bicat
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : fully_faithful_1cell f)
  : @fully_faithful_1cell (op2_bicat B) _ _ f.
Proof.
  use make_fully_faithful.
  - apply faithful_op2_bicat.
    apply fully_faithful_1cell_faithful.
    exact Hf.
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + exact (fully_faithful_1cell_inv_map Hf αf).
    + cbn.
      apply fully_faithful_1cell_inv_map_eq.
Defined.

(**
 3. Conservative 1-cells
 *)
Definition conservative_op2_bicat
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : conservative_1cell f)
  : @conservative_1cell (op2_bicat B) _ _ f.
Proof.
  intros z g₁ g₂ α Hα.
  apply to_op2_is_invertible_2cell.
  apply Hf.
  apply from_op2_is_invertible_2cell.
  exact Hα.
Defined.

(**
 4. Discrete 1-cells
 *)
Definition discrete_op2_bicat
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : discrete_1cell f)
  : @discrete_1cell (op2_bicat B) _ _ f.
Proof.
  split.
  - apply faithful_op2_bicat.
    apply Hf.
  - apply conservative_op2_bicat.
    apply Hf.
Defined.
