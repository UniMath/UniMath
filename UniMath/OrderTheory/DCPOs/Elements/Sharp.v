(******************************************************************************

 Sharp elements in a DCPO

 In this file, we define the notion of sharp elements of a DCPO. Every DCPO
 gives rise to an intrinsic apartness relation, which, in general, is neither
 tight nor cotransitive in constructive foundations. However, if we restrict
 ourselves to a subclass of elements, called the sharp elements, then we can
 prove constructively that the apartness relation is both tight and
 cotransitive.

 Reference:
 - https://arxiv.org/pdf/2106.05064.pdf

 Contents:
 1. Definition of sharp elements
 2. Characterization of sharp elements in a continuous DCPO
 3. Tightness of the intrinsic apartness relation for sharp elements
 4. Cotransitivity of the intrinsic apartness relation for sharp elements

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Core.IntrinsicApartness.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. Definition of sharp elements
 *)
Definition is_sharp
           {X : dcpo}
           (x : X)
  : hProp
  := (∀ (y z : X), y ≪ z ⇒ (y ≪ x ∨ ¬(z ⊑ x)))%logic.

(**
 2. Characterization of sharp elements in a continuous DCPO
 *)
Proposition is_sharp_continuous_dcpo
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            (x : X)
  : is_sharp x ≃ (∀ (y z : X), y ≪ z ⇒ (y ≪ x ∨ z ⊄ x))%logic.
Proof.
  use weqimplimpl.
  - intros Hx y z p.
    assert (H := unary_interpolation CX p).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro u.
    induction u as [ u [ q₁ q₂ ]].
    assert (H := unary_interpolation CX q₂).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro v.
    induction v as [ v [ r₁ r₂ ]].
    specialize (Hx u v r₁).
    revert Hx.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro s.
    induction s as [ s | s ].
    + refine (hinhpr (inl _)).
      exact (trans_way_below q₁ s).
    + cbn in s.
      refine (hinhpr (inr _)).
      use (invmap (continuous_not_specialization_weq CX z x)).
      exact (hinhpr (v ,, r₂ ,, s)).
  - intros Hx y z p.
    specialize (Hx y z p).
    revert Hx.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro q.
    induction q as [ q | q ].
    + exact (hinhpr (inl q)).
    + refine (hinhpr (inr _)).
      apply dcpo_not_specialization_le.
      exact q.
  - apply propproperty.
  - apply propproperty.
Qed.

(**
 3. Tightness of the instrinsic apartness relation for sharp elements
 *)
Lemma is_sharp_to_le
      {X : dcpo}
      (CX : continuous_dcpo_struct X)
      {x y : X}
      (Hy : is_sharp y)
      (p : ¬(x ⊄ y))
  : x ⊑ y.
Proof.
  use (invmap (continuous_dcpo_struct_le_via_approximation CX x y)).
  intros z q.
  assert (H := unary_interpolation CX q).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro H.
  induction H as [ u [ r₁ r₂ ]].
  assert (H := Hy _ _ r₁).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro H.
  induction H as [ s | s ].
  - exact s.
  - cbn in s.
    refine (fromempty (p _)).
    refine (hinhpr (_ ,, upper_set_is_scott_open CX u ,, r₂ ,, _)).
    intro w.
    apply s.
    apply way_below_to_le.
    exact w.
Qed.

Proposition is_sharp_tight_apartness
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            {x y : X}
            (Hx : is_sharp x)
            (Hy : is_sharp y)
            (p : ¬(x # y))
  : x = y.
Proof.
  use antisymm_dcpo.
  - use (is_sharp_to_le CX Hy).
    intro q.
    apply p.
    exact (hinhpr (inl q)).
  - use (is_sharp_to_le CX Hx).
    intro q.
    apply p.
    exact (hinhpr (inr q)).
Qed.

(**
 4. Cotransitivity of the intrinsic apartness relation for sharp elements
 *)
Lemma is_sharp_cotransitive_apartness_help
      {X : dcpo}
      (CX : continuous_dcpo_struct X)
      {x y z : X}
      (Hz : is_sharp z)
      (p : x ⊄ y)
  : x # z ∨ y # z.
Proof.
  assert (H := continuous_not_specialization_weq CX x y p).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro u.
  induction u as [ u [ q₁ q₂ ]].
  assert (H := unary_interpolation CX q₁).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro H.
  induction H as [ v [ r₁ r₂ ]].
  assert (H := Hz u v r₁).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro s.
  induction s as [ s | s ].
  - refine (hinhpr (inr (hinhpr (inr _)))).
    use (invmap (continuous_not_specialization_weq CX z y)).
    exact (hinhpr (u ,, s ,, q₂)).
  - refine (hinhpr (inl (hinhpr (inl _)))).
    use (invmap (continuous_not_specialization_weq CX x z)).
    exact (hinhpr (v ,, r₂ ,, s)).
Qed.

Proposition is_sharp_cotransitive_apartness
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            {x y z : X}
            (Hz : is_sharp z)
            (p : x # y)
  : x # z ∨ y # z.
Proof.
  revert p.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro p.
  induction p as [ p | p ].
  - exact (is_sharp_cotransitive_apartness_help CX Hz p).
  - assert (H := is_sharp_cotransitive_apartness_help CX Hz p).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro q.
    induction q as [ q | q ].
    + exact (hinhpr (inr q)).
    + exact (hinhpr (inl q)).
Qed.
