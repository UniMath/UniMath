(*****************************************************************

 The lift of a partial order

 We construct the lifting of partial order (adding a minimum
 element). We also show that this gives the basic operations that
 show that this operation is a comonad on pointed partial orders.
 Note that on not necessarily pointed partial orders, this
 operation would be a monad.

 Contents
 1. The order on the lift
 2. Action on morphisms
 3. The comonad structure

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.

(**
 1. The order on the lift
 *)
Definition lift_hrel
           {X : hSet}
           (PX : hrel X)
  : hrel (setcoprod X unitset).
Proof.
  intros x₁ x₂.
  induction x₁ as [ x₁ | ].
  - induction x₂ as [ x₂ | ].
    + exact (PX x₁ x₂).
    + exact hfalse.
  - exact htrue.
Defined.

Proposition lift_isPartialOrder
            {X : hSet}
            (PX : PartialOrder X)
  : isPartialOrder (lift_hrel PX).
Proof.
  repeat split.
  - intros [ x₁ | [] ] [ x₂ | [] ] [ x₃ | [] ] p q ; cbn in *.
    + exact (trans_PartialOrder PX p q).
    + exact q.
    + exact (fromempty p).
    + exact p.
    + exact tt.
    + exact tt.
    + exact tt.
    + exact tt.
  - intros [ x | [] ] ; cbn.
    + exact (refl_PartialOrder PX x).
    + exact tt.
  - intros [ x | [] ] [ y | [] ] p q ; cbn in *.
    + apply maponpaths.
      exact (antisymm_PartialOrder PX p q).
    + exact (fromempty p).
    + exact (fromempty q).
    + apply idpath.
Qed.

Definition lift_PartialOrder
           {X : hSet}
           (PX : PartialOrder X)
  : PartialOrder (setcoprod X unitset).
Proof.
  use make_PartialOrder.
  - exact (lift_hrel PX).
  - exact (lift_isPartialOrder PX).
Defined.

Definition lift_pointed_PartialOrder
           {X : hSet}
           (PX : PartialOrder X)
  : pointed_PartialOrder (setcoprod X unitset).
Proof.
  use make_pointed_PartialOrder.
  - exact (lift_PartialOrder PX).
  - exact (inr tt).
  - exact (λ _, tt).
Defined.

(**
 2. Action on morphisms
 *)
Proposition lift_strict_and_monotone_map
            {X Y : hSet}
            {f : X → Y}
            {PX : PartialOrder X}
            {PY : PartialOrder Y}
            (Pf : is_monotone PX PY f)
  : is_strict_and_monotone
      (lift_pointed_PartialOrder PX)
      (lift_pointed_PartialOrder PY)
      (coprodf1 f).
Proof.
  split.
  - intros [ x | [] ] [ y | [] ] p ; cbn in *.
    + apply Pf.
      exact p.
    + exact p.
    + exact p.
    + exact p.
  - cbn.
    apply idpath.
Qed.

(**
 3. The comonad structure
 *)
Definition lift_pointed_PartialOrder_extract
           {X : hSet}
           (PX : pointed_PartialOrder X)
           (x : setcoprod X unitset)
  : X.
Proof.
  induction x as [ x | ].
  - exact x.
  - exact (⊥_{PX}).
Defined.

Proposition is_strict_and_monotone_lift_pointed_PartialOrder_extract
            {X : hSet}
            (PX : pointed_PartialOrder X)
  : is_strict_and_monotone
      (lift_pointed_PartialOrder PX)
      PX
      (lift_pointed_PartialOrder_extract PX).
Proof.
  split.
  - intros [ x | [] ] [ y | [] ] p ; cbn in *.
    + exact p.
    + exact (fromempty p).
    + apply pointed_PartialOrder_min_point.
    + apply refl_PartialOrder.
  - cbn.
    apply idpath.
Qed.

Definition lift_pointed_PartialOrder_dupl
           {X : hSet}
           (PX : pointed_PartialOrder X)
           (x : setcoprod X unitset)
  : setcoprod (setcoprod X unitset) unitset.
Proof.
  induction x as [ x | ].
  - exact (inl (inl x)).
  - exact (inr tt).
Defined.

Proposition is_strict_and_monotone_lift_pointed_PartialOrder_dupl
            {X : hSet}
            (PX : pointed_PartialOrder X)
  : is_strict_and_monotone
      (lift_pointed_PartialOrder PX)
      (lift_pointed_PartialOrder (lift_pointed_PartialOrder PX))
      (lift_pointed_PartialOrder_dupl PX).
Proof.
  split.
  - intros [ x | [] ] [ y | [] ] p ; cbn in *.
    + exact p.
    + exact (fromempty p).
    + exact tt.
    + exact tt.
  - cbn.
    apply idpath.
Qed.
