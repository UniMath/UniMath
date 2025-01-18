(******************************************************************************

 Algebraic DCPOs

 Continuous DCPOs are those with a basis: every elements is the supremum of all
 elements that are way below it. The notion of algebraic DCPO is stronger. It
 says that there is a basis consisting of only compact elements (which are the
 elements `x` such that `x ≪ x`).

 References:
 - Section 2 in the chapter 'Domain Theory' of the Handbook for Logic in
   Computer Science, Volume 3 (https://www.cs.ox.ac.uk/files/298/handbook.pdf)
 - Section 4.6 in Domain Theory in Constructive and Predicative Univalent
   Foundations (https://tdejong.com/writings/phd-thesis.pdf)

 Contents
 1. Compact elements
 2. Algebraic DCPOs (as structure)
 3. Algebraic DCPOs (as property)
 4. Algebraic DCPOs to continuous DCPOs
 5. Structure from property for algebraic DCPOs

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. Compact elements
 *)
Definition is_compact_el
           {X : dcpo}
           (x : X)
  : hProp
  := x ≪ x.

Proposition is_compact_bot
            (X : dcppo)
  : is_compact_el (⊥_{X}).
Proof.
  apply bot_way_below.
Qed.

Proposition compact_el_way_below_le
            {X : dcpo}
            {x y : X}
            (p : is_compact_el x)
            (q : x ⊑ y)
  : x ≪ y.
Proof.
  exact (trans_way_below_le p q).
Qed.

Definition compact_elements
           (X : dcpo)
  : UU
  := ∑ (x : X), is_compact_el x.

(**
 2. Algebraic DCPOs (as structure)
 *)
Definition algebraic_dcpo_struct
           (X : dcpo)
  : UU
  := ∏ (x : X),
     ∑ (D : directed_set X),
     (∏ (i : D), is_compact_el (D i))
     ×
     is_least_upperbound X D x.

Section AlgebraicDCPOAccessors.
  Context {X : dcpo}
          (AX : algebraic_dcpo_struct X).

  Definition compact_approximating_family
             (x : X)
    : directed_set X
    := pr1 (AX x).

  Proposition is_compact_approximating_family
              (x : X)
              (i : compact_approximating_family x)
    : is_compact_el (compact_approximating_family x i).
  Proof.
    exact (pr12 (AX x) i).
  Qed.

  Proposition compact_approximating_family_lub
              (x : X)
    : ⨆ (compact_approximating_family x) = x.
  Proof.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      exact (pr122 (AX x) i).
    - use (is_least_upperbound_is_least (pr22 (AX x))).
      apply is_least_upperbound_is_upperbound.
      apply is_least_upperbound_dcpo_lub.
  Qed.

  Proposition compact_approximating_family_way_below
              (x : X)
              (i : compact_approximating_family x)
    : compact_approximating_family x i ≪ x.
  Proof.
    refine (trans_way_below_le (is_compact_approximating_family x i) _).
    exact (pr122 (AX x) i).
  Qed.
End AlgebraicDCPOAccessors.

(**
 3. Algebraic DCPOs (as property)
 *)
Definition is_algebraic_dcpo
           (X : dcpo)
  : hProp
  := ∥ algebraic_dcpo_struct X ∥.

(**
 4. Algebraic DCPOs to continuous DCPOs
 *)
Definition algebraic_dcpo_struct_to_continuous
           {X : dcpo}
           (AX : algebraic_dcpo_struct X)
  : continuous_dcpo_struct X.
Proof.
  intro x.
  refine (compact_approximating_family AX x ,, _ ,, _).
  - abstract
      (intro i ;
       apply compact_approximating_family_way_below).
  - abstract (apply AX).
Defined.

(**
 5. Structure from property for algebraic DCPOs
 *)
Proposition is_algebraic_is_directed
            {X : dcpo}
            (CX : is_algebraic_dcpo X)
            (x : X)
  : is_directed X (λ (z : ∑ (b : X), is_compact_el b ∧ b ≪ x), pr1 z).
Proof.
  revert CX.
  use factor_through_squash_hProp.
  intros CX.
  pose (D := compact_approximating_family CX x).
  split.
  - assert (H := directed_set_el D).
    revert H.
    use factor_through_squash_hProp.
    intros d.
    use hinhpr.
    refine (D d ,, _).
    split.
    + apply is_compact_approximating_family.
    + apply compact_approximating_family_way_below.
  - intros [ b₁ p₁ ] [ b₂ p₂ ].
    assert (x ⊑ ⨆ D) as q.
    {
      rewrite <- (compact_approximating_family_lub CX x).
      apply refl_dcpo.
    }
    assert (H := way_below_elem (pr2 p₁) D q).
    revert H.
    use factor_through_squash_hProp.
    intros [ c₁ r₁ ].
    assert (H := way_below_elem (pr2 p₂) D q).
    revert H.
    use factor_through_squash_hProp.
    intros [ c₂ r₂ ].
    assert (H := directed_set_top D c₁ c₂).
    revert H.
    use factor_through_squash_hProp.
    intros [ k [ s₂ s₃ ]].
    use hinhpr.
    simple refine ((D k ,, _) ,, _ ,, _).
    + split.
      * apply is_compact_approximating_family.
      * apply compact_approximating_family_way_below.
    + exact (trans_dcpo r₁ s₂).
    + exact (trans_dcpo r₂ s₃).
Qed.

Definition is_algebraic_dcpo_directed_set
           {X : dcpo}
           (CX : is_algebraic_dcpo X)
           (x : X)
  : directed_set X.
Proof.
  use make_directed_set.
  - exact (∑ (b : X), is_compact_el b ∧ b ≪ x).
  - exact (λ z, pr1 z).
  - exact (is_algebraic_is_directed CX x).
Defined.

Proposition is_algebraic_dcpo_directed_set_lub
            {X : dcpo}
            (CX : is_algebraic_dcpo X)
            (x : X)
  : ⨆ (is_algebraic_dcpo_directed_set CX x) = x.
Proof.
  revert CX.
  use factor_dep_through_squash.
  {
    intro.
    apply setproperty.
  }
  intros CX.
  pose (D := compact_approximating_family CX x).
  cbn.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intros i.
    apply way_below_to_le.
    exact (pr22 i).
  - refine (trans_dcpo _ _).
    {
      apply eq_to_le_dcpo.
      exact (!(compact_approximating_family_lub CX x)).
    }
    use dcpo_lub_is_least.
    intros i.
    use less_than_dcpo_lub ; cbn -[way_below].
    + refine (D i ,, _).
      split.
      * apply is_compact_approximating_family.
      * apply compact_approximating_family_way_below.
    + apply refl_dcpo.
Qed.

Definition is_algebraic_to_algebraic_struct
           {X : dcpo}
           (CX : is_algebraic_dcpo X)
  : algebraic_dcpo_struct X.
Proof.
  intros x.
  refine (is_algebraic_dcpo_directed_set CX x ,, _ ,, _).
  - abstract
      (intros i ;
       apply i).
  - abstract
      (pose (is_least_upperbound_dcpo_lub (is_algebraic_dcpo_directed_set CX x)) as h ;
       rewrite (is_algebraic_dcpo_directed_set_lub CX x) in h ;
       exact h).
Defined.
