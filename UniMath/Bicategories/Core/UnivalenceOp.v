(* ******************************************************************************* *)
(** * Univalence for opposite bicategories
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOp1Bicat.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition op1_bicat_idtoiso_2_1_alt
           {C : bicat}
           {X Y : op1_bicat C}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (f g : X --> Y)
  : f = g ≃ invertible_2cell f g
  := ((bicat_invertible_2cell_is_op1_bicat_invertible_2cell f g)
        ∘
        make_weq (@idtoiso_2_1 C Y X f g) (C_is_univalent_2_1 Y X f g))%weq.

Definition op1_bicat_is_univalent_2_1
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
  : is_univalent_2_1 (op1_bicat C).
Proof.
  intros X Y f g.
  use weqhomot.
  - exact (op1_bicat_idtoiso_2_1_alt C_is_univalent_2_1 f g).
  - intros p.
    induction p.
    use subtypePath.
    { apply isPredicate_is_invertible_2cell. }
    apply idpath.
Defined.

Definition op1_bicat_idtoiso_2_0_alt
           {C : bicat}
           (C_is_univalent_2_0 : is_univalent_2_0 C)
           (X Y : op1_bicat C)
  : X = Y ≃ adjoint_equivalence X Y
  := ((bicat_adjoint_equivalence_is_op1_bicat_adjoint_equivalence X Y)
        ∘ make_weq (@idtoiso_2_0 C Y X) (C_is_univalent_2_0 Y X)
        ∘ weqpathsinv0 _ _)%weq.

Definition op1_bicat_is_univalent_2_0
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (C_is_univalent_2_0 : is_univalent_2_0 C)
  : is_univalent_2_0 (op1_bicat C).
Proof.
  intros X Y.
  use weqhomot.
  - exact (op1_bicat_idtoiso_2_0_alt C_is_univalent_2_0 X Y).
  - intros p.
    induction p.
    use subtypePath.
    {
      intro ; apply isaprop_left_adjoint_equivalence.
      apply op1_bicat_is_univalent_2_1.
      exact C_is_univalent_2_1.
    }
    apply idpath.
Defined.

Definition op1_bicat_is_univalent_2
           {C : bicat}
           (C_is_univalent_2 : is_univalent_2 C)
  : is_univalent_2 (op1_bicat C).
Proof.
  split.
  - apply op1_bicat_is_univalent_2_0 ; apply C_is_univalent_2.
  - apply op1_bicat_is_univalent_2_1 ; apply C_is_univalent_2.
Defined.

Definition op2_bicat_idtoiso_2_1_alt
           {C : bicat}
           {X Y : op2_bicat C}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (f g : X --> Y)
  : f = g ≃ invertible_2cell f g
  := ((weq_op2_invertible_2cell f g)
        ∘ make_weq (@idtoiso_2_1 C _ _ g f) (C_is_univalent_2_1 _ _ g f)
        ∘ weqpathsinv0 _ _)%weq.

Definition op2_bicat_is_univalent_2_1
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
  : is_univalent_2_1 (op2_bicat C).
Proof.
  intros X Y f g.
  use weqhomot.
  - exact (op2_bicat_idtoiso_2_1_alt C_is_univalent_2_1 f g).
  - intros p.
    induction p.
    use subtypePath.
    { apply isPredicate_is_invertible_2cell. }
    apply idpath.
Defined.

Definition op2_bicat_idtoiso_2_0_alt
           {C : bicat}
           (C_is_univalent_2_0 : is_univalent_2_0 C)
           (X Y : op2_bicat C)
  : X = Y ≃ adjoint_equivalence X Y
  := ((weq_op2_adjequiv X Y)
        ∘ make_weq (@idtoiso_2_0 C X Y) (C_is_univalent_2_0 X Y))%weq.

Definition op2_bicat_is_univalent_2_0
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (C_is_univalent_2_0 : is_univalent_2_0 C)
  : is_univalent_2_0 (op2_bicat C).
Proof.
  intros X Y.
  use weqhomot.
  - exact (op2_bicat_idtoiso_2_0_alt C_is_univalent_2_0 X Y).
  - intros p.
    induction p.
    use subtypePath.
    {
      intro ; apply isaprop_left_adjoint_equivalence.
      apply op2_bicat_is_univalent_2_1.
      exact C_is_univalent_2_1.
    }
    apply idpath.
Defined.

Definition op2_bicat_is_univalent_2
           {C : bicat}
           (C_is_univalent_2 : is_univalent_2 C)
  : is_univalent_2 (op2_bicat C).
Proof.
  split.
  - apply op2_bicat_is_univalent_2_0 ; apply C_is_univalent_2.
  - apply op2_bicat_is_univalent_2_1 ; apply C_is_univalent_2.
Defined.

(**
 Being a right-adjoint is a property
 *)
Definition isaprop_internal_right_adj
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {x y : B}
           (f : x --> y)
  : isaprop (internal_right_adj f).
Proof.
  apply (isofhlevelweqf 1 (@op1_left_adjoint_weq_right_adjoint B x y f)).
  apply isaprop_left_adjoint.
  apply op1_bicat_is_univalent_2_1.
  exact HB.
Qed.
