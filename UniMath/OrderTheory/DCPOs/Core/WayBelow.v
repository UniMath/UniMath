(******************************************************************************

 The way-below relation in DCPOs

 In this file, we define the way-below relation in DCPOs. The way-below
 relation is defined as followed: an element `x` is way-below `y` (written as
 `x ≪ y`) if for every directed set `D` such that `y` is lesser than or equal
 to the supremum of `D`, we can find an element in `D` such that `x` is already
 lesser than or equal than that element.

 Note that usually, the way-below relation is formulated using subsets. However,
 just as for suprema, we take slightly different approach: we look at directed
 sets indexed by some type.

 We also look at properties of the way-below relation.

 References:
 - Section 2 in the chapter 'Domain Theory' of the Handbook for Logic in
   Computer Science, Volume 3 (https://www.cs.ox.ac.uk/files/298/handbook.pdf)
 - Section 4.2 in Domain Theory in Constructive and Predicative Univalent
   Foundations (https://tdejong.com/writings/phd-thesis.pdf)

 Contents:
 1. Definition of the way-below relation
 2. Transitivity of the way-below relation
 3. Interaction between the order of the DCPO and the way-below relation
 4. Antisymmetry of the way-below relation
 5. The bottom is way-below every element
 6. Principal lower sets for the way-below relation

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.

Local Open Scope dcpo.

(**
 1. Definition of the way-below relation
 *)
Definition way_below
           {X : dcpo}
           (x y : X)
  : hProp
  := (∀ (D : directed_set X), y ⊑ ⨆ D ⇒ ∃ (i : D), x ⊑ D i)%logic.

Notation "x ≪ y" := (way_below x y) (at level 70). (* \ll *)

Proposition way_below_elem
            {X : dcpo}
            {x y : X}
            (p : x ≪ y)
            (D : directed_set X)
            (HD : y ⊑ ⨆ D)
  : ∃ (i : D), x ⊑ D i.
Proof.
  exact (p D HD).
Qed.

Section PropertiesOfWayBelow.
  Context {X : dcpo}.

  (**
   2. Transitivity of the way-below relation
   *)
  Proposition trans_way_below
              {x y z : X}
              (p : x ≪ y)
              (q : y ≪ z)
    : x ≪ z.
  Proof.
    intros D HD.
    assert (H := way_below_elem q D HD).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros H.
    induction H as [ i H ].
    assert (H' : y ⊑ ⨆ D).
    {
      refine (trans_dcpo H _).
      use (less_than_dcpo_lub D _ i).
      apply refl_dcpo.
    }
    exact (way_below_elem p D H').
  Qed.

  (**
   3. Interaction between the order of the DCPO and the way-below relation
   *)
  Proposition trans_way_below_le
              {x y z : X}
              (p : x ≪ y)
              (q : y ⊑ z)
    : x ≪ z.
  Proof.
    intros D HD.
    exact (way_below_elem p D (trans_dcpo q HD)).
  Qed.

  Proposition trans_le_way_below
              {x y z : X}
              (p : x ⊑ y)
              (q : y ≪ z)
    : x ≪ z.
  Proof.
    intros D HD.
    assert (H := way_below_elem q D HD).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros H.
    induction H as [ i H ].
    refine (hinhpr (i ,, _)).
    exact (trans_dcpo p H).
  Qed.

  Proposition way_below_to_le
              {x y : X}
              (p : x ≪ y)
    : x ⊑ y.
  Proof.
    pose (D := nat_directed_set X (λ _, y) (λ _, refl_dcpo _)).
    assert (q : y ⊑ ⨆ D).
    {
      exact (less_than_dcpo_lub D y 0 (refl_dcpo _)).
    }
    assert (H := way_below_elem p D q).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros H.
    exact (pr2 H).
  Qed.

  (**
   4. Antisymmetry of the way-below relation
   *)
  Proposition antisymm_way_below
              {x y : X}
              (p : x ≪ y)
              (q : y ≪ x)
    : x = y.
  Proof.
    use antisymm_dcpo.
    - apply way_below_to_le.
      exact p.
    - apply way_below_to_le.
      exact q.
  Qed.
End PropertiesOfWayBelow.

(**
 5. The bottom is way-below every element
 *)
Proposition bot_way_below
            {X : dcppo}
            (x : X)
  : ⊥_{X} ≪ x.
Proof.
  intros D HD.
  assert (H := directed_set_el D).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro i.
  refine (hinhpr (i ,, _)).
  apply is_min_bottom_dcppo.
Qed.

(**
 6. Principal lower sets for the way-below relation
 *)
Definition way_below_principal
           {X : dcpo}
           (x : X)
  : UU
  := ∑ (y : X), y ≪ x.

Notation "↡ x" := (way_below_principal x) (at level 10). (* \d+9 *)

Definition way_below_principal_incl
           {X : dcpo}
           (x : X)
  : ↡ x → X
  := pr1.
