(*****************************************************************

 The unit DCPO

 In this file we give the unit DCPO and we prove properties about
 it.

 Contents
 1. Definition of the unit DCPO
 2. The unit DCPO is pointed
 3. The universal property
 4. The way below relation
 5. A basis for the unit DCPO

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. The unit DCPO
 *)
Definition unit_dcpo_struct
  : dcpo_struct unitset.
Proof.
  use make_dcpo_struct.
  - exact unit_PartialOrder.
  - intros I D HD.
    use make_lub.
    + exact tt.
    + split.
      * abstract
          (intro i ; cbn ;
           exact tt).
      * abstract
          (intros i Hi ; cbn ;
           exact tt).
Defined.

Definition unit_dcpo
  : dcpo
  := _ ,, unit_dcpo_struct.

(**
 2. The unit DCPO is pointed
 *)
Definition unit_dcppo_struct
  : dcppo_struct unitset.
Proof.
  refine (unit_dcpo_struct ,, _).
  refine (tt ,, _).
  abstract
    (intro x ;
     cbn ;
     exact tt).
Defined.

Definition unit_dcppo
  : dcppo
  := _ ,, unit_dcppo_struct.

(**
 3. The universal property
 *)
Proposition is_scott_continuous_to_unit
            {X : hSet}
            (DX : dcpo_struct X)
  : is_scott_continuous DX unit_dcpo_struct (λ _, tt).
Proof.
  split.
  - intros x y p.
    exact tt.
  - intros I D HD x Hx.
    split.
    + intro ; cbn.
      exact tt.
    + intros ? ? ; cbn.
      exact tt.
Qed.

(**
 4. The way below relation
 *)
Proposition unit_dcpo_way_below
            (x y : unit_dcpo)
  : x ≪ y.
Proof.
  intros D HD.
  assert (H := directed_set_el D).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro d.
  exact (hinhpr (d ,, tt)).
Qed.

(**
 5. A basis for the unit DCPO
 *)
Definition unit_dcpo_basis_data
  : dcpo_basis_data unit_dcpo.
Proof.
  use make_dcpo_basis_data.
  - exact unit.
  - exact (λ _, tt).
Defined.

Proposition unit_dcpo_basis_laws
  : dcpo_basis_laws unit_dcpo unit_dcpo_basis_data.
Proof.
  intro x.
  split.
  - split.
    + refine (hinhpr (tt ,, _)).
      apply unit_dcpo_way_below.
    + intros i j.
      refine (hinhpr ((tt ,, _) ,, (tt ,, tt))).
      apply unit_dcpo_way_below.
  - split.
    + intro ; exact tt.
    + intros ? ?.
      exact tt.
Qed.

Definition unit_dcpo_basis
  : dcpo_basis unit_dcpo.
Proof.
  use make_dcpo_basis.
  - exact unit_dcpo_basis_data.
  - exact unit_dcpo_basis_laws.
Defined.

Definition dcpo_continuous_struct_unit
  : continuous_dcpo_struct unit_dcpo.
Proof.
  use continuous_struct_from_basis.
  exact unit_dcpo_basis.
Defined.
