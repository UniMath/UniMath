(******************************************************************************

 Bases in DCPOs

 We define the notion of a basis of a DCPO. There are two possible approaches:
 1. A basis is given by a predicate on the elements of the DCPO
 2. We have a type of basis elements and a map from that type to the DCPO
 For both approaches, suitable requirements need to be demanded as well.

 We follow Section 4.7 in https://tdejong.com/writings/phd-thesis.pdf, and we
 use the second approach.

 We also study some properties of bases. First of all, we show that every
 continuous DCPO comes equipped with a bases and that every DCPO with a basis
 comes equipped with a continuity structure. Second, we look at the standard
 properties of continuous DCPOs and we reformulate them using the basis. For
 example, in a continuous DCPO the order relation can be characterized using
 the approximations (i.e., `x ⊑ y` if and only if for every `z` such that
 `z ≪ x`, we have `z ≪ y`). Another standard property would be interpolation:
 if we have `x ≪ y`, then we can find an element of the basis `x ≪ b ≪ y`.
 Lastly, we look at the mapping property of a DCPO with a basis. We look at
 three properties:
 1. Two maps are equal if they are equal on the basis
 2. We have `f x ⊑ g x` for every `x` if for every basis element `b` we have
   `f b ⊑ g b`
 3. If we have a monotone map from the basis to some DCPO `Y`, then we can
    extend that map to `X`.
 Note that the map from the third point is unique. The uniqueness would be
 guaranteed if the DCPO is algebraic, but not in general if the DCPO is only
 continuous.

 Contents
 1. Definition of a basis
 2. Accessors and builders for bases
 3. Bases versus continuity
 4. Approximation via bases
 5. Interpolation using bases
 6. Equality of maps via bases
 7. The order on maps via basis elements
 8. Constructing maps from their action on the basis

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

Unset Universe Checking.

Section BasisInDCPO.
  Context {X : dcpo}.

  (**
   1. Definition of a basis
   *)
  Definition dcpo_basis_data
    : UU
    := ∑ (B : UU), B → X.

  #[reversible=no] Coercion dcpo_basis_data_to_type
           (B : dcpo_basis_data)
    : UU
    := pr1 B.

  Definition dcpo_basis_data_to_dcpo
             (B : dcpo_basis_data)
             (b : B)
    : X
    := pr2 B b.

  Coercion dcpo_basis_data_to_dcpo : dcpo_basis_data >-> Funclass.

  Definition make_dcpo_basis_data
             (B : UU)
             (β : B → X)
    : dcpo_basis_data
    := B ,, β.

  Definition basis_below_element
             (B : dcpo_basis_data)
             (x : X)
    : UU
    := ∑ (b : B), B b ≪ x.

  Definition basis_below_map
             (B : dcpo_basis_data)
             (x : X)
    : basis_below_element B x → X
    := λ b, B(pr1 b).

  Definition dcpo_basis_laws
             (B : dcpo_basis_data)
    : UU
    := ∏ (x : X),
       is_directed X (basis_below_map B x)
       ×
       is_least_upperbound X (basis_below_map B x) x.

  Definition dcpo_basis
    : UU
    := ∑ (B : dcpo_basis_data), dcpo_basis_laws B.

  (**
   2. Accessors and builders for bases
   *)
  Definition make_dcpo_basis
             (B : dcpo_basis_data)
             (HB : dcpo_basis_laws B)
    : dcpo_basis
    := B ,, HB.

  #[reversible=no] Coercion dcpo_basis_to_data
           (B : dcpo_basis)
    : dcpo_basis_data
    := pr1 B.

  #[reversible=no] Coercion dcpo_basis_to_laws
           (B : dcpo_basis)
    : dcpo_basis_laws B
    := pr2 B.

  Proposition is_directed_basis
              (B : dcpo_basis)
              (x : X)
    : is_directed X (basis_below_map B x).
  Proof.
    exact (pr1 (pr2 B x)).
  Qed.

  Definition directed_set_from_basis
             (B : dcpo_basis)
             (x : X)
    : directed_set X.
  Proof.
    use make_directed_set.
    - exact (basis_below_element B x).
    - exact (basis_below_map B x).
    - exact (is_directed_basis B x).
  Defined.

  Proposition is_least_upperbound_basis
              (B : dcpo_basis)
              (x : X)
    : is_least_upperbound X (basis_below_map B x) x.
  Proof.
    exact (pr2 (pr2 B x)).
  Qed.

  Proposition approximating_basis_lub
              (B : dcpo_basis)
              (x : X)
    : ⨆ (directed_set_from_basis B x) = x.
  Proof.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      apply way_below_to_le.
      exact (pr2 i).
    - use (is_least_upperbound_is_least (is_least_upperbound_basis B x)).
      apply is_least_upperbound_is_upperbound.
      exact (is_least_upperbound_dcpo_lub (directed_set_from_basis B x)).
  Qed.
End BasisInDCPO.

Set Universe Checking.

Arguments dcpo_basis_data : clear implicits.
Arguments dcpo_basis_laws : clear implicits.
Arguments dcpo_basis : clear implicits.

(**
 3. Bases versus continuity
 *)
Definition continuous_struct_from_basis
           {X : dcpo}
           (B : dcpo_basis X)
  : continuous_dcpo_struct X.
Proof.
  intro x.
  refine (directed_set_from_basis B x ,, _ ,, _).
  - intro i.
    exact (pr2 i).
  - apply is_least_upperbound_basis.
Defined.

Definition basis_data_from_continuous_struct
           {X : dcpo}
           (CX : continuous_dcpo_struct X)
  : dcpo_basis_data X.
Proof.
  use make_dcpo_basis_data.
  - exact X.
  - exact (λ x, x).
Defined.

Proposition basis_laws_from_continuous_struct
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
  : dcpo_basis_laws X (basis_data_from_continuous_struct CX).
Proof.
  intro x.
  split.
  - split.
    + exact (nullary_interpolation CX x).
    + intros i j.
      unfold basis_below_element, basis_data_from_continuous_struct in i, j.
      cbn -[way_below] in i, j.
      assert (H := binary_interpolation CX (pr2 i) (pr2 j)).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros z.
      induction z as [ z [ p₁ [ p₂ p₃ ]]].
      refine (hinhpr ((z ,, p₃) ,, _ ,, _)).
      * apply way_below_to_le.
        exact p₁.
      * apply way_below_to_le.
        exact p₂.
  - split.
    + intros i.
      induction i as [ i p ].
      apply way_below_to_le.
      exact p.
    + intros y Hy.
      rewrite <- (approximating_family_lub CX x).
      use dcpo_lub_is_least.
      intro i.
      use (Hy (approximating_family CX x i ,, _)).
      cbn -[way_below].
      apply approximating_family_way_below.
Qed.

Definition basis_from_continuous_struct
           {X : dcpo}
           (CX : continuous_dcpo_struct X)
  : dcpo_basis X.
Proof.
  use make_dcpo_basis.
  - exact (basis_data_from_continuous_struct CX).
  - exact (basis_laws_from_continuous_struct CX).
Defined.

Section BasisProperties.
  Context {X : dcpo}
          (B : dcpo_basis X).

  (**
   4. Approximation via bases
   *)

  (**
   We can characterize the order of the DCPO using the way-below relation
   and the basis
   *)
  Proposition dcpo_basis_le_via_approximation
              (x y : X)
    : x ⊑ y
      ≃
      ∀ (z : B), (B z ≪ x ⇒ B z ≪ y)%logic.
  Proof.
    use weqimplimpl.
    - intros p z q.
      exact (trans_way_below_le q p).
    - intros H.
      rewrite <- (approximating_basis_lub B x).
      use dcpo_lub_is_least.
      intro i.
      apply way_below_to_le.
      apply (H (pr1 i) (pr2 i)).
    - apply propproperty.
    - apply propproperty.
  Qed.

  Let CX : continuous_dcpo_struct X := continuous_struct_from_basis B.

  (**
   5. Interpolation using bases
   *)
  Proposition basis_nullary_interpolation
              (x : X)
    : ∃ (i : B), B i ≪ x.
  Proof.
    assert (H := nullary_interpolation CX x).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro y.
    induction y as [ y p ].
    assert (H := directed_set_el (directed_set_from_basis B y)).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro i.
    induction i as [ i q ].
    refine (hinhpr (i ,, _)).
    exact (trans_way_below q p).
  Qed.

  Proposition basis_unary_interpolation
              {x y : X}
              (p : x ≪ y)
    : ∃ (i : B), x ≪ B i ∧ B i ≪ y.
  Proof.
    assert (H := unary_interpolation CX p).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro z.
    induction z as [ z [ q₁ q₂ ] ].
    assert (r : y ⊑ ⨆ directed_set_from_basis B y).
    {
      rewrite approximating_basis_lub.
      apply refl_dcpo.
    }
    assert (H := q₂ (directed_set_from_basis B y) r).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro i.
    induction i as [ [ i s₁ ] s₂ ].
    refine (hinhpr (i ,, _ ,, _)).
    - exact (trans_way_below_le q₁ s₂).
    - exact s₁.
  Qed.

  Proposition basis_binary_interpolation
              {x₁ x₂ y : X}
              (p₁ : x₁ ≪ y)
              (p₂ : x₂ ≪ y)
    : ∃ (i : B), x₁ ≪ B i ∧ x₂ ≪ B i ∧ B i ≪ y.
  Proof.
    assert (H := binary_interpolation CX p₁ p₂).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro z.
    induction z as [ z [ q₁ [ q₂ q₃ ] ] ].
    assert (H := basis_unary_interpolation q₃).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro i.
    induction i as [ i [ r₁ r₂ ]].
    refine (hinhpr (i ,, _ ,, _ ,, _)).
    - exact (trans_way_below q₁ r₁).
    - exact (trans_way_below q₂ r₁).
    - exact r₂.
  Qed.

  (**
   6. Equality of maps via bases
   *)

  (**
   Two maps from a continuous DCPO to any DCPO are equal if they
   are equal on the basis elements.
   *)
  Proposition scott_continuous_map_eq_on_basis
              {Y : dcpo}
              {f g : scott_continuous_map X Y}
              (p : ∏ (i : B), f (B i) = g (B i))
    : f = g.
  Proof.
    use eq_scott_continuous_map.
    intro x.
    refine (maponpaths f (!((approximating_basis_lub B x))) @ _).
    refine (_ @ maponpaths g (approximating_basis_lub B x)).
    rewrite !scott_continuous_map_on_lub.
    use antisymm_dcpo.
    - use dcpo_lub_is_least ; cbn.
      intro i.
      use less_than_dcpo_lub ; cbn.
      + exact i.
      + unfold basis_below_map.
        rewrite p.
        apply refl_dcpo.
    - use dcpo_lub_is_least ; cbn.
      intro i.
      use less_than_dcpo_lub ; cbn.
      + exact i.
      + unfold basis_below_map.
        rewrite p.
        apply refl_dcpo.
  Qed.

  Proposition map_eq_on_basis_if_scott_continuous
              {Y : dcpo}
              {f g : X → Y}
              (p : ∏ (i : B), f (B i) = g (B i))
              (Hf : is_scott_continuous X Y f)
              (Hg : is_scott_continuous X Y g)
              (x : X)
    : f x = g x.
  Proof.
    exact (maponpaths
             (λ z, pr1 z x)
             (@scott_continuous_map_eq_on_basis Y (f ,, Hf) (g ,, Hg) p)).
  Qed.

  (**
   7. The order on maps via basis elements
   *)
  Proposition scott_continuous_map_le_on_basis
              {Y : dcpo}
              {f g : scott_continuous_map X Y}
              (p : ∏ (i : B), f (B i) ⊑ g (B i))
              (x : X)
    : f x ⊑ g x.
  Proof.
    rewrite (maponpaths f (!((approximating_basis_lub B x)))).
    rewrite (maponpaths g (!(approximating_basis_lub B x))).
    rewrite !scott_continuous_map_on_lub.
    use dcpo_lub_is_least ; cbn.
    intro i.
    use less_than_dcpo_lub ; cbn.
    - exact i.
    - unfold basis_below_map.
      apply p.
  Qed.

  Proposition map_le_on_basis_if_scott_continuous
              {Y : dcpo}
              {f g : X → Y}
              (p : ∏ (i : B), f (B i) ⊑ g (B i))
              (Hf : is_scott_continuous X Y f)
              (Hg : is_scott_continuous X Y g)
              (x : X)
    : f x ⊑ g x.
  Proof.
    exact (@scott_continuous_map_le_on_basis Y (f ,, Hf) (g ,, Hg) p x).
  Qed.

  (**
   8. Constructing maps from their action on the basis
   *)
  Section ScottContinuousFromBasis.
    Context {Y : dcpo}
            (f : B → Y)
            (Hf : ∏ (i₁ i₂ : B), B i₁ ≪ B i₂ → f i₁ ⊑ f i₂).

    Proposition is_directed_map_from_basis
                (x : X)
      : is_directed Y (λ (i : basis_below_element B x), f (pr1 i)).
    Proof.
      split.
      - assert (H := directed_set_el (directed_set_from_basis B x)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intro i.
        exact (hinhpr i).
      - intros i j.
        induction i as [i Hix].
        induction j as [j Hjx].
        assert (H := basis_binary_interpolation Hix Hjx).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intro k.
        induction k as  [ k [ p [ q r ]]].
        refine (hinhpr ((k ,, r) ,, _ ,, _)).
        + apply Hf.
          exact p.
        + apply Hf.
          exact q.
    Qed.

    Definition map_directed_set_from_basis
               (x : X)
      : directed_set Y.
    Proof.
      use make_directed_set.
      - exact (basis_below_element B x).
      - exact (λ i, f (pr1 i)).
      - exact (is_directed_map_from_basis x).
    Defined.

    Definition map_from_basis
               (x : X)
      : Y
      := ⨆ (map_directed_set_from_basis x).

    Proposition map_from_basis_monotone
                (x₁ x₂ : X)
                (p : x₁ ⊑ x₂)
      : map_from_basis x₁ ⊑ map_from_basis x₂.
    Proof.
      unfold map_from_basis.
      use dcpo_lub_is_least ; cbn.
      intro i.
      use less_than_dcpo_lub.
      - refine (pr1 i ,, _).
        exact (trans_way_below_le (pr2 i) p).
      - cbn.
        apply refl_dcpo.
    Qed.

    Proposition map_from_basis_lub
                (D : directed_set X)
      : map_from_basis (⨆ D)
        =
        ⨆_{ D} (map_from_basis ,, map_from_basis_monotone).
    Proof.
      unfold map_from_basis.
      use antisymm_dcpo.
      - unfold map_from_basis.
        use dcpo_lub_is_least ; cbn.
        intro i.
        induction i as [ i p ] ; cbn.
        assert (H := unary_interpolation CX p).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intro H.
        induction H as [ j [ q₁ q₂ ]].
        assert (H := q₂ D (refl_dcpo _)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intro k.
        induction k as [ k r ].
        use less_than_dcpo_lub.
        + exact k.
        + cbn.
          use less_than_dcpo_lub.
          * refine (i ,, _).
            exact (trans_way_below_le q₁ r).
          * cbn.
            apply refl_dcpo.
      - unfold map_from_basis.
        use dcpo_lub_is_least ; cbn.
        intro i.
        use dcpo_lub_is_least ; cbn.
        intro j.
        induction j as [ j p ] ; cbn.
        use less_than_dcpo_lub.
        + refine (j ,, _).
          refine (trans_way_below_le p _).
          use less_than_dcpo_lub.
          * exact i.
          * apply refl_dcpo.
        + cbn.
          apply refl_dcpo.
    Qed.

    Proposition is_scott_continuous_map_from_basis
      : is_scott_continuous (pr2 X) (pr2 Y) map_from_basis.
    Proof.
      use make_is_scott_continuous.
      - exact map_from_basis_monotone.
      - exact map_from_basis_lub.
    Qed.

    Definition scott_continuous_map_from_basis
      : scott_continuous_map X Y
      := map_from_basis ,, is_scott_continuous_map_from_basis.

    Proposition scott_continuous_map_from_basis_le
                (i : B)
      : scott_continuous_map_from_basis (B i) ⊑ f i.
    Proof.
      use dcpo_lub_is_least ; cbn.
      intro j.
      induction j as [ j p ] ; cbn.
      apply Hf.
      exact p.
    Qed.

    Proposition scott_continuous_map_from_basis_greatest
      (g : scott_continuous_map X Y)
      (Hg : ∏ (i : B), g (B i) ⊑ f i)
      (x : X)
      : g x ⊑ scott_continuous_map_from_basis x.
    Proof.
      assert (g x ⊑ g (⨆ directed_set_from_basis B x)) as p.
      {
        apply (is_monotone_scott_continuous_map g).
        rewrite (approximating_basis_lub B x).
        apply refl_dcpo.
      }
      refine (trans_dcpo p _).
      rewrite scott_continuous_map_on_lub.
      cbn ; unfold map_from_basis.
      use dcpo_lub_is_least.
      intro i.
      cbn in i.
      use less_than_dcpo_lub.
      - exact i.
      - apply Hg.
    Qed.

  End ScottContinuousFromBasis.
End BasisProperties.
