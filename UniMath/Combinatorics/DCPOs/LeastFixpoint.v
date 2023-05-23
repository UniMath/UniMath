#[local] Unset Universe Checking.
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
Require Import UniMath.Combinatorics.DCPOs.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.DCPOBasics.
Require Import UniMath.Combinatorics.DCPOs.ScottContinuous.

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

  Proposition bot_iteration_map_S
              (n : ℕ)
    : bot_iteration_map (S n) = f (bot_iteration_map n).
  Proof.
    apply idpath.
  Qed.

  Lemma is_monotone_bot_iteration_map_S
        (n : ℕ)
    : bot_iteration_map n ≤ f (bot_iteration_map n).
  Proof.
    induction n as [ | n IHn ].
    - apply is_min_bottom_dcppo.
    - exact (is_monotone_scott_continuous_map f IHn).
  Qed.

  Lemma is_monotone_bot_iteration_map_help
        (n k : ℕ)
    : bot_iteration_map n ≤ bot_iteration_map (n + k).
  Proof.
    induction k as [ | k IHk ].
    - rewrite natplusr0.
      apply refl_dcpo.
    - refine (trans_dcpo IHk _).
      rewrite natplusnsm.
      apply is_monotone_bot_iteration_map_S.
  Qed.

  Proposition is_monotone_bot_iteration_map
              {n m : ℕ}
              (p : (n ≤ m)%nat)
    : bot_iteration_map n ≤ bot_iteration_map m.
  Proof.
    pose (nat_le_diff p) as H.
    induction H as [ k H ].
    rewrite <- H.
    apply is_monotone_bot_iteration_map_help.
  Qed.

  Proposition is_directed_bot_iteration_map
    : is_directed X bot_iteration_map.
  Proof.
    split.
    - exact (hinhpr 5).
    - intros i j.
      apply hinhpr.
      refine (i + j ,, _ ,, _).
      + use is_monotone_bot_iteration_map.
        apply natlehnplusnm.
      + use is_monotone_bot_iteration_map.
        apply natlehmplusnm.
  Qed.

  Definition bot_iteration_directed_set
    : directed_set X.
  Proof.
    simple refine (ℕ ,, (_ ,, _)).
    - exact bot_iteration_map.
    - exact is_directed_bot_iteration_map.
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
      + cbn.
        use (@is_monotone_bot_iteration_map i (S i)).
        apply natlehnsn.
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
    - rewrite bot_iteration_map_S.
      rewrite <- p.
      exact (is_monotone_scott_continuous_map f IHn).
  Qed.
End FixpointTheorem.
