(**
 Morphisms in op2 bicat

 Contents
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 3. Conservative 1-cells
 4. Discrete 1-cells
 5. Adjunctions
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

(**
 5. Adjunctions
 *)
Definition op2_left_adjoint_right_adjoint_is_left_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : @left_adjoint (op2_bicat B) _ _ f)
  : @left_adjoint B _ _ (left_adjoint_right_adjoint Hf).
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact f.
  - exact (left_adjoint_counit Hf).
  - exact (left_adjoint_unit Hf).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       exact (internal_triangle2 Hf)).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       exact (internal_triangle1 Hf)).
Defined.

Definition op2_left_adjoint_to_right_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : @left_adjoint (op2_bicat B) _ _ f)
  : @internal_right_adj B _ _ f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (left_adjoint_right_adjoint Hf).
  - exact (left_adjoint_counit Hf).
  - exact (left_adjoint_unit Hf).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       exact (internal_triangle2 Hf)).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       exact (internal_triangle1 Hf)).
Defined.

Definition right_adjoint_to_op2_left_adjoint
           {B : bicat}
           {x y : B}
           {f : x --> y}
           (Hf : @internal_right_adj B _ _ f)
  : @left_adjoint (op2_bicat B) _ _ f.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (internal_right_adj_left_adjoint Hf).
  - exact (internal_right_adj_counit Hf).
  - exact (internal_right_adj_unit Hf).
  - abstract
      (cbn ;
       rewrite !vassocr ;
       exact (pr22 Hf)).
  - abstract
      (cbn ;
       rewrite !vassocr ;
       exact (pr12 Hf)).
Defined.


Definition op2_left_adjoint_weq_right_adjoint
           {B : bicat}
           {x y : B}
           (f : x --> y)
  : @left_adjoint (op2_bicat B) _ _ f ≃ @internal_right_adj B _ _ f.
Proof.
  use make_weq.
  - exact op2_left_adjoint_to_right_adjoint.
  - use isweq_iso.
    + exact right_adjoint_to_op2_left_adjoint.
    + abstract
        (intro Hf ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply idpath).
    + abstract
        (intro Hf ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply idpath).
Defined.
