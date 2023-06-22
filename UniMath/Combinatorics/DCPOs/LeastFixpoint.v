(*****************************************************************

 Fixpoints in DCPO

 In this file, we prove the classical fixpoint theorem for DCPOs
 that says that every Scott continuous map has a least fixpoint.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.Posets.PointedPosets.
Require Import UniMath.Combinatorics.DCPOs.Core.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.Core.Basics.
Require Import UniMath.Combinatorics.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

Section FixpointTheorem.
  Context {X : dcppo}
          (f : scott_continuous_map X X).

  Definition bot_iteration_map
             (n : ℕ)
    : X.
  Proof.
    induction n as [ | n IHn ].
    - exact (⊥_{X}).
    - exact (f IHn).
  Defined.

  Lemma is_monotone_bot_iteration_map_S
        (n : ℕ)
    : bot_iteration_map n ≤ f (bot_iteration_map n).
  Proof.
    induction n as [ | n IHn ].
    - apply is_min_bottom_dcppo.
    - exact (is_monotone_scott_continuous_map f IHn).
  Qed.

  Definition bot_iteration_directed_set
    : directed_set X.
  Proof.
    use nat_directed_set.
    - exact bot_iteration_map.
    - apply is_monotone_bot_iteration_map_S.
  Defined.

  Definition least_fixpoint
    : X
    := ⨆ bot_iteration_directed_set.

  Proposition is_fixpoint_least_fixpoint
    : f least_fixpoint = least_fixpoint.
  Proof.
    unfold least_fixpoint.
    rewrite scott_continuous_map_on_lub.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      cbn ; intro i.
      use less_than_dcpo_lub.
      + exact (S i).
      + apply refl_dcpo.
    - use dcpo_lub_is_least.
      cbn ; intro i.
      use less_than_dcpo_lub.
      + exact i.
      + apply is_monotone_bot_iteration_map_S.
  Qed.

  Theorem is_least_fixpoint_least_fixpoint
          (x : X)
          (p : f x = x)
    : least_fixpoint ≤ x.
  Proof.
    use dcpo_lub_is_least ; cbn.
    intro n.
    induction n as [ | n IHn ].
    - apply is_min_bottom_dcppo.
    - rewrite <- p.
      exact (is_monotone_scott_continuous_map f IHn).
  Qed.
End FixpointTheorem.
