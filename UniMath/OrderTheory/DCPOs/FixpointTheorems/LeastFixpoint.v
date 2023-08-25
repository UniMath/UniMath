(*****************************************************************

 Fixpoints in DCPO

 In this file, we prove the classical fixpoint theorem for DCPOs
 that says that every Scott continuous map has a least fixpoint.
 We also show that we have a continuous function that assigns to
 every Scott continuous function the least fixpoint. The
 construction of this map is based on the proof of Theorem
 1.2.17 of 'The Lambda Calculus, its Syntax and Semantics' by
 Barendregt.

 The idea is as follows: we already defined numerous combinators
 for Scott continuous maps (lambda, application), and we reuse
 those to reproduce the construction of the least fixpoint. The
 following steps are key:
 - [iterate_scott_continuous_map]: this function assigns to every
   `f` and `n` the map `f ∘ ... ∘ f` (`n` times). For this
   definition, we use the lambda combinator of Scott continuous
   maps.
 - [least_fixpoint_scott_continuous_map_on_N]: this function
   assigns to every `f` and `n` the point `f(...f(⊥_{X})...)`. We
   use the evaluation, pairing, and the function defined in the
   previous point for it.
 - [least_fixpoint_scott_continuous_map]: this function takes the
   least upperbound for every `n` of all the functions defined in
   the previous point.
 This is the same construction as used in the Knaster-Tarski
 fixpoint theorem, and we prove that in
 [least_fixpoint_scott_continuous_map_is_least_fixpoint].

 Contents
 1. The least fixpoint
 2. Pointed DCPPO of fixpoints
 3. Continuous map that assigns to a function its least fixpoint

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Examples.Fixpoints.
Require Import UniMath.OrderTheory.DCPOs.Examples.Exponentials.
Require Import UniMath.OrderTheory.DCPOs.Examples.BinaryProducts.

Local Open Scope dcpo.

Section FixpointTheorem.
  Context {X : dcppo}
          (f : scott_continuous_map X X).

  (**
   1. The least fixpoint
   *)
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
    : bot_iteration_map n ⊑ f (bot_iteration_map n).
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
    : least_fixpoint ⊑ x.
  Proof.
    use dcpo_lub_is_least ; cbn.
    intro n.
    induction n as [ | n IHn ].
    - apply is_min_bottom_dcppo.
    - rewrite <- p.
      exact (is_monotone_scott_continuous_map f IHn).
  Qed.

  Definition bottom_element_fixpoint_dcpo
    : bottom_element (fixpoint_dcpo f).
  Proof.
    simple refine ((least_fixpoint ,, _) ,, _).
    - apply is_fixpoint_least_fixpoint.
    - exact (λ x, is_least_fixpoint_least_fixpoint _ (pr2 x)).
  Defined.

  (**
   2. Pointed DCPPO of fixpoints
   *)
  Definition fixpoint_dcppo
    : dcppo
    := _ ,, pr2 (fixpoint_dcpo f) ,, bottom_element_fixpoint_dcpo.
End FixpointTheorem.

(**
 3. Continuous map that assigns to a function its least fixpoint
 *)
Definition iterate_on_pt_scott_continuous_map
           {X : dcpo}
           (n : ℕ)
  : scott_continuous_map (X × dcpo_funspace X X) X.
Proof.
  induction n as [ | n IHn ].
  - exact π₁.
  - exact (comp_scott_continuous_map
             ⟨ eval_scott_continuous_map X X , π₂ ⟩
             IHn).
Defined.

Proposition iterate_on_pt_scott_continuous_map_fun_pt
            {X : dcpo}
            (n : ℕ)
            (f : scott_continuous_map X X)
            (x : X)
  : iterate_on_pt_scott_continuous_map n (f x ,, f)
    =
    f (iterate_on_pt_scott_continuous_map n (x ,, f)).
Proof.
  revert x.
  induction n as [ | n IHn ].
  - intro ; cbn.
    apply idpath.
  - intro x.
    simpl ; unfold prodtofuntoprod ; simpl.
    apply IHn.
Qed.

Definition iterate_scott_continuous_map
           {X : dcppo}
           (n : ℕ)
  : scott_continuous_map (dcpo_funspace X X) (dcpo_funspace X X)
  := lam_scott_continuous_map (iterate_on_pt_scott_continuous_map n).

Definition iterate_scott_continuous_map_S
           {X : dcppo}
           (n : ℕ)
           (f : scott_continuous_map X X)
           (x : X)
  : pr1 (iterate_scott_continuous_map (S n) f) x
    =
    f (pr1 (iterate_scott_continuous_map n f) x).
Proof.
  simpl ; unfold prodtofuntoprod ; simpl.
  exact (iterate_on_pt_scott_continuous_map_fun_pt n f x).
Qed.

Definition least_fixpoint_scott_continuous_map_on_N
           {X : dcppo}
           (n : ℕ)
  : dcpo_funspace (dcpo_funspace X X) X
  := comp_scott_continuous_map
       ⟨ constant_scott_continuous_map _ ⊥_{X} , iterate_scott_continuous_map n ⟩
       (eval_scott_continuous_map _ _).

Definition least_fixpoint_scott_continuous_map_directed_set
           (X : dcppo)
  : directed_set (dcpo_funspace (dcpo_funspace X X) X).
Proof.
  use nat_directed_set.
  - exact least_fixpoint_scott_continuous_map_on_N.
  - abstract
      (intros i f ;
       simpl ; unfold prodtofuntoprod ; simpl ;
       use is_monotone_scott_continuous_map ;
       split ; [ apply is_min_bottom_dcppo | ] ;
       intro ;
       apply refl_dcpo).
Defined.

Definition least_fixpoint_scott_continuous_map
           (X : dcppo)
  : dcpo_funspace (dcpo_funspace X X) X
  := ⨆ least_fixpoint_scott_continuous_map_directed_set X.

Proposition least_fixpoint_scott_continuous_map_is_least_fixpoint_on_N
            {X : dcppo}
            (f : scott_continuous_map X X)
            (n : ℕ)
  : pr1 (least_fixpoint_scott_continuous_map_on_N n) f
    =
    bot_iteration_directed_set f n.
Proof.
  induction n as [ | n IHn ].
  - apply idpath.
  - refine (_ @ maponpaths _ IHn).
    simpl ; unfold prodtofuntoprod ; simpl.
    apply (iterate_on_pt_scott_continuous_map_fun_pt n f).
Qed.

Proposition least_fixpoint_scott_continuous_map_is_least_fixpoint
            {X : dcppo}
            (f : scott_continuous_map X X)
  : pr1 (least_fixpoint_scott_continuous_map X) f
    =
    least_fixpoint f.
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intro i ; cbn in i.
    use less_than_dcpo_lub.
    + exact i.
    + rewrite <- least_fixpoint_scott_continuous_map_is_least_fixpoint_on_N.
      apply refl_dcpo.
  - use dcpo_lub_is_least.
    intro i ; cbn in i.
    use less_than_dcpo_lub.
    + exact i.
    + rewrite <- least_fixpoint_scott_continuous_map_is_least_fixpoint_on_N.
      apply refl_dcpo.
Qed.
