(******************************************************************************

 Continuous DCPOs

 We define the notion of continuous DCPOs. A DCPO is called continuous if every
 element is the least upper bound of a directed set consisting only of elements
 way below that element. Note that there are multiple ways to formulate this
 definition in univalent foundations:
 1. We can formulate it as structure [continuous_dcpo_struct]
 2. We can formulate it as a property [is_continuous_dcpo]
 There also is a third way, called pseudocontinuity, which also is a property.

 Furthermore, we study properties of continuous DCPOs. The first properties
 that we look at, characterize the order relation and the way-below relation in
 continuous DCPOs. The last properties that we look at, are about interpolation.
 These come in three flavors:
 1. Nullary interpolation: given an element, we can find some element that is
    way-below the original element.
 2. Unary interpolation: given two elements `x` and `y` such that `x ⊑ y`, we
    can find an element inbetween `x` and `y`: `x ≪ i ≪ y`.
 3. Binary interpolation: given three elements `x₁, x₂, y` such that `x₁ ⊑ y`
    and `x₂ ⊑ y`, we can find an element `i` such that `x₁ ≪ i ≪ y` and
    `x₂ ≪ i ≪ y`.
 Note that we can generalize interpolation to finite sets. These interpolation
 properties are useful when proving stuff about continuous DCPOs.

 We also show that if a DCPO is continuous (as a property), then we  have
 a canonical continuity structure on that DCPO. We define the approximating
 family for `x` to consist of all elements `y` such that `y ≪ x`. We can show
 that this set is directed, and for that we use that we know that the DCPO is
 continuous (as a property). We can use this assumption, because being directed
 is a proposition. In addition, we can also show that the supremum of the
 approximating family of `x` is indeed `x`. Here we again use the continuity,
 and since equality of elements in DCPOs is a proposition, we can indeed do so.
 Intuitively, what is happening here, is that there is a canonical choice for
 the approximating family, and this allows us to choose a continuity structure
 if we know one exists.

 References:
 - Section 2 in the chapter 'Domain Theory' of the Handbook for Logic in
   Computer Science, Volume 3 (https://www.cs.ox.ac.uk/files/298/handbook.pdf)
 - Section 4.4 and 4.5  in Domain Theory in Constructive and Predicative
   Univalent Foundations (https://tdejong.com/writings/phd-thesis.pdf)

 Contents
 1. Continuous DCPOs (as structure)
 2. Continuous DCPOs (as property)
 3. Equivalent formulations of inequality in continuous DCPOs
 4. Characterization of the way-below relation in continuous DCPOs
 5. Nullary interpolation
 6. Unary interpolation
 7. Binary interpolation
 8. Continuity structure from the property

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.

Local Open Scope dcpo.

(**
 1. Continuous DCPOs (as structure)
 *)
Definition continuous_dcpo_struct
           (X : dcpo)
  : UU
  := ∏ (x : X),
     ∑ (D : directed_set X),
     (∏ (i : D), D i ≪ x)
     ×
     is_least_upperbound X D x.

(**
 2. Continuous DCPOs (as property)
 *)
Definition is_continuous_dcpo
           (X : dcpo)
  : hProp
  := ∥ continuous_dcpo_struct X ∥.

Section ContinuousDCPOAccessors.
  Context {X : dcpo}
          (CX : continuous_dcpo_struct X).

  Definition approximating_family
             (x : X)
    : directed_set X
    := pr1 (CX x).

  Proposition approximating_family_way_below
              (x : X)
              (i : approximating_family x)
    : approximating_family x i ≪ x.
  Proof.
    exact (pr12 (CX x) i).
  Qed.

  Proposition approximating_family_lub
              (x : X)
    : ⨆ (approximating_family x) = x.
  Proof.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      apply way_below_to_le.
      exact (approximating_family_way_below x i).
    - use (is_least_upperbound_is_least (pr22 (CX x))).
      apply is_least_upperbound_is_upperbound.
      apply is_least_upperbound_dcpo_lub.
  Qed.
End ContinuousDCPOAccessors.

Section PropertiesContinuousDCPO.
  Context {X : dcpo}
          (CX : continuous_dcpo_struct X).

  (**
   3. Equivalent formulations of inequality in continuous DCPOs
   *)
  Proposition continuous_dcpo_struct_le_to_way_below
              {x y : X}
              (p : x ⊑ y)
              (i : approximating_family CX x)
    : approximating_family CX x i ≪ y.
  Proof.
    use (trans_way_below_le _ p).
    apply approximating_family_way_below.
  Qed.

  Proposition continuous_dcpo_struct_approx_way_below_to_le
              {x y : X}
              (p : ∏ (i : approximating_family CX x),
                   approximating_family CX x i ≪ y)
              (i : approximating_family CX x)
    : approximating_family CX x i ⊑ y.
  Proof.
    use way_below_to_le.
    apply p.
  Qed.

  Proposition continuous_dcpo_struct_approx_le_to_le
              {x y : X}
              (p : ∏ (i : approximating_family CX x),
                   approximating_family CX x i ⊑ y)
    : x ⊑ y.
  Proof.
    rewrite <- (approximating_family_lub CX x).
    use dcpo_lub_is_least.
    exact p.
  Qed.

  Proposition continuous_dcpo_struct_le_weq_approx_le
              (x y : X)
    : x ⊑ y
      ≃
      ∀ (i : approximating_family CX x),
      approximating_family CX x i ⊑ y.
  Proof.
    use weqimplimpl.
    - intros p i.
      apply continuous_dcpo_struct_approx_way_below_to_le.
      intro j.
      apply continuous_dcpo_struct_le_to_way_below.
      exact p.
    - intros H.
      apply continuous_dcpo_struct_approx_le_to_le.
      exact H.
    - apply propproperty.
    - apply propproperty.
  Qed.

  Proposition continuous_dcpo_struct_le_weq_approx_way_below
              (x y : X)
    : x ⊑ y
      ≃
      ∀ (i : approximating_family CX x),
      approximating_family CX x i ≪ y.
  Proof.
    use weqimplimpl.
    - exact continuous_dcpo_struct_le_to_way_below.
    - intros H.
      apply continuous_dcpo_struct_approx_le_to_le.
      intro i.
      apply continuous_dcpo_struct_approx_way_below_to_le.
      exact H.
    - apply propproperty.
    - apply propproperty.
  Qed.

  Proposition continuous_dcpo_struct_le_via_approximation
              (x y : X)
    : x ⊑ y
      ≃
      ∀ (z : X), (z ≪ x ⇒ z ≪ y)%logic.
  Proof.
    use weqimplimpl.
    - intros p z q.
      exact (trans_way_below_le q p).
    - intros H.
      rewrite <- (approximating_family_lub CX x).
      use dcpo_lub_is_least.
      pose (D := approximating_family CX x).
      fold D.
      intro i.
      apply way_below_to_le.
      apply (H (D i)).
      apply approximating_family_way_below.
    - apply propproperty.
    - apply propproperty.
  Qed.

  (**
   4. Characterization of the way-below relation in continuous DCPOs
   *)
  Proposition continuous_dcpo_struct_way_below
              (x y : X)
    : x ≪ y
      ≃
      ∃ (i : approximating_family CX y), x ⊑ approximating_family CX y i.
  Proof.
    use weqimplimpl.
    - intro p.
      apply (p (approximating_family CX y)).
      rewrite approximating_family_lub.
      apply refl_dcpo.
    - use factor_through_squash.
      {
        apply propproperty.
      }
      intro H.
      induction H as [ i p ].
      refine (trans_le_way_below p _).
      apply approximating_family_way_below.
    - apply propproperty.
    - apply propproperty.
  Qed.

  (**
   5. Nullary interpolation
   *)
  Proposition nullary_interpolation
              (x : X)
    : ∃ (y : X), y ≪ x.
  Proof.
    pose (D := approximating_family CX x).
    assert (H := directed_set_el D).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro i.
    refine (hinhpr (D i ,, _)).
    apply approximating_family_way_below.
  Qed.

  (**
   6. Unary interpolation
   *)
  Section UnaryInterpolation.
    Context {x y : X}
            (p : x ≪ y).

    Let D : directed_set X := approximating_family CX y.
    Let D_a : D → directed_set X := λ i, approximating_family CX (D i).

    Proposition unary_interpolation_cofinal_lem
                {i₁ i₂ : D}
                (q : D i₁ ⊑ D i₂)
                (j₁ : D_a i₁)
      : D_a i₁ j₁ ≪ ⨆ (D_a i₂).
    Proof.
      refine (trans_way_below_le _ _).
      - apply approximating_family_way_below.
      - refine (trans_dcpo q _).
        unfold D_a.
        rewrite approximating_family_lub.
        apply refl_dcpo.
    Qed.

    Proposition unary_interpolation_cofinal
                {i₁ i₂ : D}
                (q : D i₁ ⊑ D i₂)
                (j₁ : D_a i₁)
      : ∃ (j₂ : D_a i₂), D_a i₁ j₁ ⊑ D_a i₂ j₂.
    Proof.
      use (unary_interpolation_cofinal_lem q j₁ (D_a i₂)).
      apply refl_dcpo.
    Qed.

    Proposition is_directed_unary_interpolation_directed_set
      : is_directed X (λ (ij : ∑ (i : D), D_a i), D_a (pr1 ij) (pr2 ij)).
    Proof.
      split.
      - assert (H := directed_set_el D).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intro i.
        assert (H := directed_set_el (D_a i)).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intro j.
        exact (hinhpr (i ,, j)).
      - intros ij₁ ij₂.
        induction ij₁ as [ i₁ j₁ ].
        induction ij₂ as [ i₂ j₂ ].
        assert (H := directed_set_top D i₁ i₂).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intros k.
        induction k as [ k [ q₁ q₂ ]].
        assert (H := unary_interpolation_cofinal q₁ j₁).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intros H₁.
        induction H₁ as [ l₁ H₁ ].
        assert (H := unary_interpolation_cofinal q₂ j₂).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intros H₂.
        induction H₂ as [ l₂ H₂ ].
        assert (H := directed_set_top (D_a k) l₁ l₂).
        revert H.
        use factor_through_squash ; [ apply propproperty | ].
        intros H.
        induction H as [ m [ r₁ r₂ ]].
        refine (hinhpr ((k ,, m) ,, _ ,, _)).
        + exact (trans_dcpo H₁ r₁).
        + exact (trans_dcpo H₂ r₂).
    Qed.

    Definition unary_interpolation_directed_set
      : directed_set X.
    Proof.
      use make_directed_set.
      - exact (∑ (i : D), D_a i).
      - exact (λ ij, D_a (pr1 ij) (pr2 ij)).
      - exact is_directed_unary_interpolation_directed_set.
    Defined.

    Proposition unary_interpolation
      : ∃ (z : X), x ≪ z ∧ z ≪ y.
    Proof.
      assert (s : y ⊑ ⨆ unary_interpolation_directed_set).
      {
        apply continuous_dcpo_struct_approx_le_to_le.
        intro i.
        use continuous_dcpo_struct_approx_le_to_le.
        intro j.
        use less_than_dcpo_lub.
        {
          exact (i ,, j).
        }
        apply refl_dcpo.
      }
      assert (H := p unary_interpolation_directed_set s).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro i.
      induction i as [ i r ].
      refine (hinhpr (D (pr1 i) ,, _ ,, _)).
      - refine (trans_le_way_below r _).
        apply approximating_family_way_below.
      - apply approximating_family_way_below.
    Qed.
  End UnaryInterpolation.

  (**
   7. Binary interpolation
   *)
  Proposition binary_interpolation
              {x₁ x₂ y : X}
              (p₁ : x₁ ≪ y)
              (p₂ : x₂ ≪ y)
    : ∃ (z : X), x₁ ≪ z ∧ x₂ ≪ z ∧ z ≪ y.
  Proof.
    pose (D := approximating_family CX y).
    assert (s : y ⊑ ⨆ D).
    {
      unfold D.
      rewrite approximating_family_lub.
      apply refl_dcpo.
    }
    assert (z₁ := unary_interpolation p₁).
    revert z₁.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro z₁.
    induction z₁ as [ z₁ [ q₁ r₁ ]].
    assert (H := r₁ D s).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ i₁ H₁ ].
    assert (z₂ := unary_interpolation p₂).
    revert z₂.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro z₂.
    induction z₂ as [ z₂ [ q₂ r₂ ]].
    assert (H := r₂ D s).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro H.
    induction H as [ i₂ H₂ ].
    assert (H := directed_set_top D i₁ i₂).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros H.
    induction H as [ k [ w₁ w₂ ]].
    refine (hinhpr (D k ,, _ ,, _ ,, _)).
    - exact (trans_way_below_le q₁ (trans_dcpo H₁ w₁)).
    - exact (trans_way_below_le q₂ (trans_dcpo H₂ w₂)).
    - apply approximating_family_way_below.
  Qed.
End PropertiesContinuousDCPO.

(**
 8. Continuity structure from the property
 *)
Proposition is_continuous_dcpo_is_directed
            {X : dcpo}
            (CX : is_continuous_dcpo X)
            (x : X)
  : is_directed X (λ (z : ∑ (b : X), b ≪ x), pr1 z).
Proof.
  revert CX.
  use factor_through_squash_hProp.
  intros CX.
  pose (D := approximating_family CX x).
  split.
  - assert (H := directed_set_el D).
    revert H.
    use factor_through_squash_hProp.
    intros d.
    use hinhpr.
    refine (D d ,, _).
    apply approximating_family_way_below.
  - intros [ b₁ p₁ ] [ b₂ p₂ ].
    assert (x ⊑ ⨆ D) as q.
    {
      rewrite <- (approximating_family_lub CX x).
      apply refl_dcpo.
    }
    assert (H := way_below_elem p₁ D q).
    revert H.
    use factor_through_squash_hProp.
    intros [ c₁ r₁ ].
    assert (H := way_below_elem p₂ D q).
    revert H.
    use factor_through_squash_hProp.
    intros [ c₂ r₂ ].
    assert (H := directed_set_top D c₁ c₂).
    revert H.
    use factor_through_squash_hProp.
    intros [ k [ s₂ s₃ ]].
    use hinhpr.
    simple refine ((D k ,, _) ,, _ ,, _).
    + apply approximating_family_way_below.
    + exact (trans_dcpo r₁ s₂).
    + exact (trans_dcpo r₂ s₃).
Qed.

Definition is_continuous_dcpo_directed_set
           {X : dcpo}
           (CX : is_continuous_dcpo X)
           (x : X)
  : directed_set X.
Proof.
  use make_directed_set.
  - exact (∑ (b : X), b ≪ x).
  - exact (λ z, pr1 z).
  - exact (is_continuous_dcpo_is_directed CX x).
Defined.

Proposition is_continuous_dcpo_directed_set_lub
            {X : dcpo}
            (CX : is_continuous_dcpo X)
            (x : X)
  : ⨆ (is_continuous_dcpo_directed_set CX x) = x.
Proof.
  revert CX.
  use factor_dep_through_squash.
  {
    intro.
    apply setproperty.
  }
  intros CX.
  pose (D := approximating_family CX x).
  cbn.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intros i.
    apply way_below_to_le.
    exact (pr2 i).
  - refine (trans_dcpo _ _).
    {
      apply eq_to_le_dcpo.
      exact (!(approximating_family_lub CX x)).
    }
    use dcpo_lub_is_least.
    intros i.
    use less_than_dcpo_lub ; cbn -[way_below].
    + refine (D i ,, _).
      apply approximating_family_way_below.
    + apply refl_dcpo.
Qed.

Definition is_continuous_to_continuous_struct
           {X : dcpo}
           (CX : is_continuous_dcpo X)
  : continuous_dcpo_struct X.
Proof.
  intros x.
  refine (is_continuous_dcpo_directed_set CX x ,, _ ,, _).
  - abstract
      (intros i ;
       apply i).
  - abstract
      (pose (is_least_upperbound_dcpo_lub (is_continuous_dcpo_directed_set CX x)) as h ;
       rewrite (is_continuous_dcpo_directed_set_lub CX x) in h ;
       exact h).
Defined.
