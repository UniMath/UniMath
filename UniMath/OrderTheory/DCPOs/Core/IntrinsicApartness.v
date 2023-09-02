(******************************************************************************

 The intrinsic apartness relation of a DCPO

 Every DCPO gives rise to an intrinsic apartness relation. To define it, we
 take the following steps
 1. We define the specialization preorder. An element `x` is a specialization of
    an element `y` if every open set that contains `x` also contains `y`.
 2. We define the `does not specialize` relation. Classically, this relation is
    equivalent to the negation of the specialization preorder, but
    constructively, that is not true.
 3. We define the intrinsic apartness relation.

 Note that in general, the intrinsic apartness relation is neither tight nor
 cotransitive in constructive foundations. See Theorem 5.6 in
     https://arxiv.org/pdf/2106.05064.pdf

 We also prove some properties of every relation that we define in this file.

 Contents
 1. The specialization preorder
 2. Properties of the specialization preorder
 3. The 'does not specialize' relation
 4. Properties of the 'does not specialize' relation
 5. The intrinsic apartness relation
 6. Properties of the intrinsic apartness relation

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. The specialization preorder
 *)
Definition dcpo_specialization
           {X : dcpo}
           (x y : X)
  : hProp
  := (∀ (P : X → hProp), is_scott_open P ⇒ P x ⇒ P y)%logic.

Notation "x ⊑s y" := (dcpo_specialization x y) (at level 70) : dcpo.

(**
 2. Properties of the specialization preorder
 *)
Section PropertiesSpecialization.
  Context {X : dcpo}.

  Proposition refl_dcpo_specialization
              (x : X)
    : x ⊑s x.
  Proof.
    intros P HP Px.
    exact Px.
  Qed.

  Proposition trans_dcpo_specialization
              {x y z : X}
              (p : x ⊑s y)
              (q : y ⊑s z)
    : x ⊑s z.
  Proof.
    intros P HP Px.
    apply (q P HP).
    apply (p P HP Px).
  Qed.

  Proposition le_dcpo_specialization
              {x y : X}
              (p : x ⊑ y)
    : x ⊑s y.
  Proof.
    intros P HP Px.
    exact (is_scott_open_upper_set HP Px p).
  Qed.

  Proposition le_dcpo_specialization_equiv
              (CX : continuous_dcpo_struct X)
              (x y : X)
    : x ⊑ y ≃ x ⊑s y.
  Proof.
    use weqimplimpl.
    - exact le_dcpo_specialization.
    - intros p.
      use (invmap (continuous_dcpo_struct_le_via_approximation CX x y)).
      intro z.
      intro q.
      exact (p _ (upper_set_is_scott_open CX z) q).
    - apply propproperty.
    - apply propproperty.
  Qed.
End PropertiesSpecialization.

(**
 3. The 'does not specialize' relation
 *)
Definition dcpo_not_specialization
           {X : dcpo}
           (x y : X)
  : hProp
  := (∃ (P : X → hProp), is_scott_open P ∧ P x ∧ ¬(P y))%logic.

Notation "x ⊄ y" := (dcpo_not_specialization x y) (at level 70) : dcpo. (* \nsubset *)

(**
 4. Properties of the 'does not specialize' relation
 *)
Section PropertiesNotSpecialization.
  Context {X : dcpo}.

  Proposition irrefl_dcpo_not_specialization
              (x : X)
    : ¬(x ⊄ x).
  Proof.
    use factor_through_squash.
    {
      apply isapropempty.
    }
    intro P.
    induction P as [ P [ HP [ p n ]]].
    exact (n p).
  Qed.

  Proposition dcpo_not_specialization_le
              {x y : X}
              (p : x ⊄ y)
    : ¬(x ⊑ y).
  Proof.
    intro q.
    revert p.
    use factor_through_squash.
    {
      apply isapropempty.
    }
    intros P.
    induction P as  [ P [ HP [ Px Py ]]].
    refine (Py _).
    exact (is_scott_open_upper_set HP Px q).
  Qed.

  Proposition continuous_not_specialization_weq
              (CX : continuous_dcpo_struct X)
              (x y : X)
    : x ⊄ y ≃ (∃ (b : X), b ≪ x ∧ ¬(b ⊑ y))%logic.
  Proof.
    use weqimplimpl.
    - use factor_through_squash.
      {
        apply propproperty.
      }
      intros P.
      induction P as [ P [ HP [ p₁ p₂ ]]] ; cbn in p₂.
      pose (D := approximating_family CX x).
      assert (HD : P (⨆ D)).
      {
        unfold D.
        rewrite approximating_family_lub.
        exact p₁.
      }
      assert (H := is_scott_open_lub_inaccessible HP D HD).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro i.
      induction i as [ i Pi ].
      refine (hinhpr (D i ,, _ ,, _)).
      + apply approximating_family_way_below.
      + intro n.
        apply p₂.
        apply (is_scott_open_upper_set HP Pi n).
    - use factor_through_squash.
      {
        apply propproperty.
      }
      intro b.
      induction b as [ b [ p₁ p₂ ]] ; cbn in p₂.
      apply hinhpr.
      refine (_ ,, upper_set_is_scott_open CX b ,, p₁ ,, _).
      intro p.
      apply p₂.
      apply way_below_to_le.
      exact p.
    - apply propproperty.
    - apply propproperty.
  Qed.
End PropertiesNotSpecialization.

(**
 5. The intrinsic apartness relation
 *)
Definition dcpo_intrinsic_apartness
           {X : dcpo}
           (x y : X)
  : hProp
  := dcpo_not_specialization x y ∨ dcpo_not_specialization y x.

Notation "x # y" := (dcpo_intrinsic_apartness x y).

(**
 6. Properties of the intrinsic apartness relation
 *)
Section PropertiesApartness.
  Context {X : dcpo}.

  Proposition irrefl_intrinsic_apartness
              (x : X)
    : ¬(x # x).
  Proof.
    use factor_through_squash.
    {
      apply isapropempty.
    }
    intros p.
    induction p as [ p | p ].
    - apply (irrefl_dcpo_not_specialization x).
      exact p.
    - apply (irrefl_dcpo_not_specialization x).
      exact p.
  Qed.

  Proposition symmetric_intrinsic_apartness
              {x y : X}
              (p : x # y)
    : y # x.
  Proof.
    revert p.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros p.
    induction p as [ p | p ].
    - exact (hinhpr (inr p)).
    - exact (hinhpr (inl p)).
  Qed.

  Proposition intrinsic_apartness_not_eq
              {x y : X}
              (p : x # y)
    : ¬(x = y).
  Proof.
    intro q.
    induction q.
    exact (irrefl_intrinsic_apartness x p).
  Qed.
End PropertiesApartness.
