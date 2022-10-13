(**
 Morphisms in op1 bicat

 Contents
 1. Adjunctions
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
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Local Open Scope cat.

(**
 1. Adjunctions
 *)
Definition op1_left_adjoint_to_right_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : @left_adjoint B _ _ f)
  : @internal_right_adj (op1_bicat B) _ _ f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (left_adjoint_right_adjoint Hf).
  - exact (left_adjoint_unit Hf).
  - exact (left_adjoint_counit Hf).
  - exact (internal_triangle2 Hf).
  - exact (internal_triangle1 Hf).
Defined.

Definition right_adjoint_to_op1_left_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : @internal_right_adj (op1_bicat B) _ _ f)
  : @left_adjoint B _ _ f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (internal_right_adj_left_adjoint Hf).
  - exact (internal_right_adj_unit Hf).
  - exact (internal_right_adj_counit Hf).
  - exact (pr22 Hf).
  - exact (pr12 Hf).
Defined.

Definition op1_left_adjoint_weq_right_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
  : @left_adjoint B _ _ f ≃ @internal_right_adj (op1_bicat B) _ _ f.
Proof.
  use make_weq.
  - exact op1_left_adjoint_to_right_adjoint.
  - use isweq_iso.
    + exact right_adjoint_to_op1_left_adjoint.
    + intro.
      apply idpath.
    + intro.
      apply idpath.
Defined.
