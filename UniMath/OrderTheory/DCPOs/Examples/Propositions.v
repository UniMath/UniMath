(*****************************************************************

 hProp as a DCPO

 In this file, we show that hProp is a DCPO. This DCPO is also
 known as the Sierpinski space.

 Contents:
 1. hProp is a DCPO
 2. hProp is pointed

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

(**
 1. hProp is a DCPO
 *)
Proposition isPartialOrder_hProp
  : isPartialOrder (λ (P₁ P₂ : hProp), (P₁ ⇒ P₂)%logic).
Proof.
  refine ((_ ,, _) ,, _).
  - exact (λ P₁ P₂ P₃ f g x, g(f x)).
  - exact (λ P x, x).
  - exact (λ P₁ P₂ f g, hPropUnivalence _ _ f g).
Qed.

Definition hProp_PartialOrder
  : PartialOrder hProp_set.
Proof.
  use make_PartialOrder.
  - exact (λ (P₁ P₂ : hProp), P₁ ⇒ P₂)%logic.
  - exact isPartialOrder_hProp.
Defined.

Definition hProp_lub
           {D : UU}
           {f : D → hProp}
           (Hf : is_directed hProp_PartialOrder f)
  : lub hProp_PartialOrder f.
Proof.
  use make_lub.
  - exact (∃ (d : D), f d).
  - refine (_ ,, _).
    + exact (λ d x, hinhpr (d ,, x)).
    + abstract
        (intros P HP ;
         use factor_through_squash ; [ apply propproperty | ] ;
         intro x ;
         exact (HP (pr1 x) (pr2 x))).
Defined.

Definition hProp_dcpo_struct
  : dcpo_struct hProp_set.
Proof.
  use make_dcpo_struct.
  - exact hProp_PartialOrder.
  - exact (λ D f Hf, hProp_lub Hf).
Defined.

Definition hProp_dcpo
  : dcpo
  := _ ,, hProp_dcpo_struct.

(**
 2. hProp is pointed
 *)
Definition hProp_dcppo
  : dcppo.
Proof.
  refine (_ ,, hProp_dcpo_struct ,, hfalse ,, _).
  abstract
    (intros P ;
     exact fromempty).
Defined.
