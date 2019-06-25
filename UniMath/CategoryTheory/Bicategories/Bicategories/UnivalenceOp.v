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
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OpMorBicat.

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
    use subtypeEquality.
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
    use subtypeEquality.
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
  := ((bicat_invertible_2cell_is_op2_bicat_invertible_2cell f g)
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
    use subtypeEquality.
    { apply isPredicate_is_invertible_2cell. }
    apply idpath.
Defined.

Definition op2_bicat_idtoiso_2_0_alt
           {C : bicat}
           (C_is_univalent_2_0 : is_univalent_2_0 C)
           (X Y : op2_bicat C)
  : X = Y ≃ adjoint_equivalence X Y
  := ((bicat_adjoint_equivalence_is_op2_bicat_adjoint_equivalence X Y)
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
    use subtypeEquality.
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
