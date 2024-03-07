(******************************************************************************

 Compact Basis

 In this file, we define the notion of a compact basis. The difference between
 a basis and a compact basis is that a compact basis is required to only
 consist of compact elements. We show that every compact basis gives the DCPO
 the structure of an algebraic DCPO.

 In addition, we also look at how to define maps using a compact basis. If we
 have a basis on a DCPO, then every monotone map from the basis to a DCPO can
 be extended to a Scott continuous map. However, this Scott continuous is in
 general not unique. If the basis only consists of compact elements, then the
 acquired map is actually unique. In addition, we have a stronger computation
 rule [scott_continuous_map_from_compact_basis_eq]. For ordinary basis, this
 rule only holds up to inequality.

 References:
 - Section 4.8 in https://tdejong.com/writings/phd-thesis.pdf

 Contents
 1. Compact basis
 2. Accessors and builders for compact bases
 3. Every compact basis gives rise to a basis
 4. Compact bases from bases of which every element is compact
 5. Compact bases versus algebraicity
 6. Constructing maps from their action on the basis

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.
Require Import UniMath.OrderTheory.DCPOs.Basis.Algebraic.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.

Local Open Scope dcpo.

Section CompactBasisInDCPO.
  Context {X : dcpo}.

  (**
   1. Compact basis
   *)
  Definition compact_basis_le_element
             (B : dcpo_basis_data X)
             (x : X)
    : UU
    := ∑ (b : B), B b ⊑ x.

  Definition compact_basis_le_map
             (B : dcpo_basis_data X)
             (x : X)
    : compact_basis_le_element B x → X
    := λ b, B(pr1 b).

  Definition compact_basis_laws
             (B : dcpo_basis_data X)
    : UU
    := (∏ (b : B), is_compact_el (B b))
       ×
       (∏ (x : X), is_directed X (compact_basis_le_map B x))
       ×
       (∏ (x : X), is_least_upperbound X (compact_basis_le_map B x) x).

  Definition compact_basis
    : UU
    := ∑ (B : dcpo_basis_data X), compact_basis_laws B.

  (**
   2. Accessors and builders for compact bases
   *)
  Definition make_compact_basis
             (B : dcpo_basis_data X)
             (HB : compact_basis_laws B)
    : compact_basis
    := B ,, HB.

  #[reversible=no] Coercion compact_basis_to_data
           (B : compact_basis)
    : dcpo_basis_data X
    := pr1 B.

  #[reversible=no] Coercion compact_basis_to_laws
           (B : compact_basis)
    : compact_basis_laws B
    := pr2 B.

  Proposition is_compact_el_basis
              (B : compact_basis)
              (b : B)
    : is_compact_el (B b).
  Proof.
    exact (pr12 B b).
  Qed.

  Proposition is_directed_compact_basis
              (B : compact_basis)
              (x : X)
    : is_directed X (compact_basis_le_map B x).
  Proof.
    exact (pr122 B x).
  Qed.

  Definition directed_set_from_compact_basis
             (B : compact_basis)
             (x : X)
    : directed_set X.
  Proof.
    use make_directed_set.
    - exact (compact_basis_le_element B x).
    - exact (compact_basis_le_map B x).
    - exact (is_directed_compact_basis B x).
  Defined.

  Proposition is_least_upperbound_compact_basis
              (B : compact_basis)
              (x : X)
    : is_least_upperbound X (compact_basis_le_map B x) x.
  Proof.
    exact (pr222 B x).
  Qed.

  Proposition approximating_compact_basis_lub
              (B : compact_basis)
              (x : X)
    : ⨆ (directed_set_from_compact_basis B x) = x.
  Proof.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      exact (pr2 i).
    - use (is_least_upperbound_is_least (is_least_upperbound_compact_basis B x)).
      apply is_least_upperbound_is_upperbound.
      exact (is_least_upperbound_dcpo_lub (directed_set_from_compact_basis B x)).
  Qed.
End CompactBasisInDCPO.

Arguments compact_basis_laws : clear implicits.
Arguments compact_basis : clear implicits.

(**
 3. Every compact basis gives rise to a basis
 *)
Proposition compact_basis_to_dcpo_basis_laws
           {X : dcpo}
           (B : compact_basis X)
  : dcpo_basis_laws X B.
Proof.
  intro x.
  split.
  - split.
    + assert (H := directed_set_el (directed_set_from_compact_basis B x)).
      revert H.
      use factor_through_squash ; [ apply propproperty | ].
      intro i.
      refine (hinhpr (pr1 i ,, _)).
      exact (trans_way_below_le (is_compact_el_basis B (pr1 i)) (pr2 i)).
    + intros i j.
      assert (H := directed_set_top
                     (directed_set_from_compact_basis B x)
                     (pr1 i ,, way_below_to_le (pr2 i))
                     (pr1 j ,, way_below_to_le (pr2 j))).
      revert H.
      use factor_through_squash ; [ apply propproperty | ].
      intro k.
      induction k as [ k [ p q ]].
      refine (hinhpr ((pr1 k ,, _) ,, p ,, q)).
      exact (trans_way_below_le (is_compact_el_basis B (pr1 k)) (pr2 k)).
  - split.
    + intro i.
      exact (pr1 (is_least_upperbound_compact_basis B x) (pr1 i ,, way_below_to_le (pr2 i))).
    + intros y p.
      use (pr2 (is_least_upperbound_compact_basis B x) y).
      intro i.
      use (p (pr1 i ,, _)).
      exact (trans_way_below_le (is_compact_el_basis B (pr1 i)) (pr2 i)).
Qed.

Definition compact_basis_to_dcpo_basis
           {X : dcpo}
           (B : compact_basis X)
  : dcpo_basis X.
Proof.
  use make_dcpo_basis.
  - exact B.
  - exact (compact_basis_to_dcpo_basis_laws B).
Defined.

(**
 4. Compact bases from bases of which every element is compact
 *)
Section BasisToCompact.
  Context {X : dcpo}
          (B : dcpo_basis X)
          (HB : ∏ (b : B), is_compact_el (B b)).

  Proposition dcpo_basis_with_compact_to_compact_basis_laws
    : compact_basis_laws X B.
  Proof.
    refine (_ ,, _ ,, _).
    - exact HB.
    - intro x.
      split.
      + assert (H := directed_set_el (directed_set_from_basis B x)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b p ].
        refine (hinhpr (b ,, _)).
        apply way_below_to_le.
        exact p.
      + intros i j.
        induction i as [ b₁ p₁ ].
        induction j as [ b₂ p₂ ].
        assert (q₁ : B b₁ ≪ x).
        {
          refine (compact_el_way_below_le _ p₁).
          apply HB.
        }
        assert (q₂ : B b₂ ≪ x).
        {
          refine (compact_el_way_below_le _ p₂).
          apply HB.
        }
        assert (H := directed_set_top (directed_set_from_basis B x) (b₁ ,, q₁) (b₂ ,, q₂)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros t.
        induction t as [ [ t r₁ ] [ r₂ r₃ ]].
        refine (hinhpr ((t ,, _) ,, (r₂ ,, r₃))).
        apply way_below_to_le.
        exact r₁.
    - intro x.
      split.
      + intros b.
        exact (pr2 b).
      + intros y Hy.
        use (pr2 (is_least_upperbound_basis B x) y).
        intros b.
        induction b as [ b p ].
        use (Hy (b ,, _)).
        apply way_below_to_le.
        exact p.
  Qed.

  Definition dcpo_basis_with_compact_to_compact_basis
    : compact_basis X.
  Proof.
    use make_compact_basis.
    - exact B.
    - exact dcpo_basis_with_compact_to_compact_basis_laws.
  Defined.
End BasisToCompact.

(**
 5. Compact bases versus algebraicity
 *)
Definition algebraic_struct_from_compact_basis
           {X : dcpo}
           (B : compact_basis X)
  : algebraic_dcpo_struct X.
Proof.
  intro x.
  refine (directed_set_from_compact_basis B x ,, _ ,, _).
  - intro i.
    apply is_compact_el_basis.
  - apply is_least_upperbound_compact_basis.
Defined.

Definition compact_basis_data_from_algebraic_struct
           {X : dcpo}
           (AX : algebraic_dcpo_struct X)
  : dcpo_basis_data X.
Proof.
  use make_dcpo_basis_data.
  - exact (compact_elements X).
  - exact (λ x, pr1 x).
Defined.

Proposition compact_basis_laws_from_algebraic_struct
            {X : dcpo}
            (AX : algebraic_dcpo_struct X)
  : compact_basis_laws X (compact_basis_data_from_algebraic_struct AX).
Proof.
  pose (CX := algebraic_dcpo_struct_to_continuous AX).
  simple refine (_ ,, _ ,, _).
  - intro b.
    exact (pr2 b).
  - intro x.
    pose (D := compact_approximating_family AX x).
    split.
    + assert (H := directed_set_el D).
      revert H.
      use factor_through_squash ; [ apply propproperty | ].
      intro y.
      simple refine (hinhpr ((D y ,, _) ,, _)) ; cbn -[way_below].
      * apply is_compact_approximating_family.
      * rewrite <- (compact_approximating_family_lub AX x).
        use (less_than_dcpo_lub D _ y).
        apply refl_dcpo.
    + intros y z.
      induction y as [ [ y Hy ] p ].
      induction z as [ [ z Hz ] q ].
      assert (Hxy : y ⊑ ⨆ D).
      {
        unfold D.
        rewrite (compact_approximating_family_lub AX x).
        exact p.
      }
      assert (Hxz : z ⊑ ⨆ D).
      {
        unfold D.
        rewrite (compact_approximating_family_lub AX x).
        exact q.
      }
      assert (H₁ := Hy D Hxy).
      revert H₁.
      use factor_through_squash ; [ apply propproperty | ].
      intros i.
      induction i as [ i ri ].
      assert (H₂ := Hz D Hxz).
      revert H₂.
      use factor_through_squash ; [ apply propproperty | ].
      intros j.
      induction j as [ j rj ].
      assert (H₃ := directed_set_top D i j).
      revert H₃.
      use factor_through_squash ; [ apply propproperty | ].
      intros k.
      induction k as [ k [ s₁ s₂ ] ].
      simple refine (hinhpr (((D k ,, _) ,, _) ,, (_ ,, _))).
      * apply is_compact_approximating_family.
      * cbn.
        rewrite <- (compact_approximating_family_lub AX x).
        use (less_than_dcpo_lub _ _ k).
        apply refl_dcpo.
      * exact (trans_dcpo ri s₁).
      * exact (trans_dcpo rj s₂).
  - intro x.
    split.
    + intros i.
      induction i as [ i p ].
      exact p.
    + intros y Hy.
      rewrite <- (compact_approximating_family_lub AX x).
      use dcpo_lub_is_least.
      intro i.
      simple refine (Hy ((compact_approximating_family AX x i ,, _) ,, _)).
      * apply is_compact_approximating_family.
      * apply way_below_to_le.
        apply compact_approximating_family_way_below.
Qed.

Definition compact_basis_from_algebraic_struct
           {X : dcpo}
           (AX : algebraic_dcpo_struct X)
  : compact_basis X.
Proof.
  use make_compact_basis.
  - exact (compact_basis_data_from_algebraic_struct AX).
  - exact (compact_basis_laws_from_algebraic_struct AX).
Defined.

(**
 6. Constructing maps from their action on the basis
 *)
Proposition scott_continuous_map_from_compact_basis_eq
            {X : dcpo}
            (B : compact_basis X)
            {Y : dcpo}
            (f : B → Y)
            (Hf : ∏ (i₁ i₂ : B), B i₁ ≪ B i₂ → f i₁ ⊑ f i₂)
            (i : B)
  : scott_continuous_map_from_basis
      (compact_basis_to_dcpo_basis B)
      f
      Hf
      (B i)
    =
    f i.
Proof.
  use antisymm_dcpo.
  - apply scott_continuous_map_from_basis_le.
  - use less_than_dcpo_lub.
    + refine (i ,, _).
      apply is_compact_el_basis.
    + apply refl_dcpo.
Qed.

Definition scott_continuous_map_from_compact_basis_ump
           {X : dcpo}
           (B : compact_basis X)
           {Y : dcpo}
           (f : B → Y)
           (Hf : ∏ (i₁ i₂ : B), B i₁ ≪ B i₂ → f i₁ ⊑ f i₂)
  : ∃! (g : scott_continuous_map X Y),
    ∏ (i : B), g (B i) = f i.
Proof.
  pose (CB := compact_basis_to_dcpo_basis B).
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; use impred ; intro ; apply setproperty | ] ;
       use (scott_continuous_map_eq_on_basis CB) ;
       intro i ;
       exact (pr2 φ₁ i @ !(pr2 φ₂ i))).
  - refine (scott_continuous_map_from_basis CB f Hf ,, _).
    apply scott_continuous_map_from_compact_basis_eq.
Defined.
