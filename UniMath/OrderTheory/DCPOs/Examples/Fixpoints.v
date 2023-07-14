(*****************************************************************

 The DCPO of fixpoints

 Let `f` be a Scott continuous map from a DCPO `X` to itself. Then
 there is a DCPO whose inhabitants are fixpoints of `f`. To
 construct this DCPO, it suffices to show that fixpoints are
 closed under least upperbounds. This allows us to construct the
 desired DCPO as a subDCPO.

 Contents
 1. Fixpoints are closed under least upperbounds
 2. The DCPO of fixpoint of a Scott continuous maps

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Examples.SubDCPO.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

Section FixpointDCPO.
  Context {X : dcpo}
          (f : scott_continuous_map X X).

  (**
   1. Fixpoints are closed under least upperbounds
   *)
  Proposition lub_fixpoint
              (D : directed_set X)
              (HD : ∏ (d : D), f(D d) = D d)
    : f (⨆ D) = ⨆ D.
  Proof.
    rewrite scott_continuous_map_on_lub.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i ; cbn in i ; cbn.
      use less_than_dcpo_lub.
      + exact i.
      + exact (eq_to_le_dcpo (HD i)).
    - use dcpo_lub_is_least.
      intro i ; cbn in i ; cbn.
      use less_than_dcpo_lub.
      + exact i.
      + exact (eq_to_le_dcpo (!(HD i))).
  Qed.

  (**
   2. The DCPO of fixpoint of a Scott continuous maps
   *)
  Definition fixpoint_dcpo
    : dcpo
    := sub_dcpo X (λ x, f x = x)%logic lub_fixpoint.
End FixpointDCPO.
