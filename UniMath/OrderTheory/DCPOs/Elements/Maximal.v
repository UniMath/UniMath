(******************************************************************************

 Maximal elements in a DCPO

 In this file, we define maximal elements in DCPOs. In classical foundations,
 an element `x` is called maximal if for every `y` such that `x ⊑ y`, we have
 that `x = y`. However, constructively, there is a better notion, namely that
 of a strongly maximal element (see https://arxiv.org/pdf/2106.05064.pdf).

 We also prove some properties of strongly maximal elements. In particular, we
 show that they are sharp and that they are maximal if the DCPO is continuous.

Contents
 1. Maximal elements
 2. Hausdorff separated elements
 3. Properties of Hausdorff separated elements
 4. Hausdorff separatedness in continuous DCPOs
 5. Strongly maximal elements
 6. Strongly maximal elements are sharp
 7. The intrinsic apartness relation on strongly maximal elements
 8. In a continuous DCPO, strongly maximal elements are maximal
 9. A simplified strong maximality condition in a continuous DCPO
10. Apartness for strongly maximal elements is Hausdorff separatedness

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Core.IntrinsicApartness.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.
Require Import UniMath.OrderTheory.DCPOs.Elements.Sharp.

Local Open Scope dcpo.

Definition are_disjoint
           {X : UU}
           (P₁ P₂ : X → hProp)
  : hProp
  := (∀ (z : X), ¬(P₁ z ∧ P₂ z))%logic.

Proposition symm_are_disjoint
            {X : UU}
            {P₁ P₂ : X → hProp}
            (H : are_disjoint P₁ P₂)
  : are_disjoint P₂ P₁.
Proof.
  intros z p.
  exact (H z (pr2 p ,, pr1 p)).
Qed.

(** * 1. Maximal elements *)
Definition is_maximal
           {X : dcpo}
           (x : X)
  : hProp
  := (∀ (y : X), x ⊑ y ⇒ y ⊑ x)%logic.

(** * 2. Hausdorff separated elements *)
Definition is_hausdorff_separated
           {X : dcpo}
           (x y : X)
  : hProp
  := ∃ (P₁ P₂ : scott_open_set X), P₁ x ∧ P₂ y ∧ are_disjoint P₁ P₂.

(** * 3. Properties of Hausdorff separated elements *)
Section PropertiesHausdorffSeparated.
  Context {X : dcpo}.

  Proposition irrefl_is_hausdorff_separated
              (x : X)
    : ¬(is_hausdorff_separated x x).
  Proof.
    use factor_through_squash.
    {
      apply isapropempty.
    }
    intros H.
    induction H as [ P₁ [ P₂ [ Px [ Px' H ]]]].
    exact (H x (Px ,, Px')).
  Qed.

  Proposition symm_is_hausdorff_separated
              {x y : X}
              (H : is_hausdorff_separated x y)
    : is_hausdorff_separated y x.
  Proof.
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros H.
    induction H as [ P₁ [ P₂ [ Px [ Py H ]]]].
    refine (hinhpr (P₂ ,, P₁ ,, Py ,, Px ,, _)).
    apply symm_are_disjoint.
    exact H.
  Qed.

  Proposition is_hausdorff_separated_not_le
              {x y : X}
              (H : is_hausdorff_separated x y)
    : ¬(x ⊑ y).
  Proof.
    intro p.
    revert H.
    use factor_through_squash.
    {
      apply isapropempty.
    }
    intros H.
    induction H as [ P₁ [ P₂ [ Px [ Py H ]]]].
    refine (H y (_ ,, _)).
    - refine (is_scott_open_upper_set P₁ Px p).
    - exact Py.
  Qed.

  Lemma is_hausdorff_separated_le (x y z : X) :
    y ⊑ z → is_hausdorff_separated y x → is_hausdorff_separated z x.
  Proof.
    intros Hyz.
    use factor_through_squash_hProp.
    intros (S1 & S2 & H1 & H2 & Hdisj).
    apply hinhpr.
    use (S1,, S2,, _,, H2,, Hdisj).
    exact (is_scott_open_upper_set S1 H1 Hyz).
  Qed.
End PropertiesHausdorffSeparated.

(** * 4. Hausdorff separatedness in continuous DCPOs *)
Definition from_hausdorff_separated_continuous_dcpo
           {X : dcpo}
           (B : dcpo_basis X)
           (x y : X)
  : is_hausdorff_separated x y
    →
    (∃ (b₁ b₂ : B),
     B b₁ ≪ x
     ∧
     B b₂ ≪ y
     ∧
     ¬(∃ (t : B), B b₁ ≪ B t ∧ B b₂ ≪ B t))%logic.
Proof.
  use factor_through_squash_hProp.
  intros (S1 & S2 & H1 & H2 & Hdisj).
  pose (H := is_scott_open_lub_inaccessible S1 (directed_set_from_basis B x)).
  rewrite approximating_basis_lub in H.
  specialize (H H1).
  revert H.
  use factor_through_squash_hProp.
  intros ( i₁ & Hi₁ ).
  pose (H := is_scott_open_lub_inaccessible S2 (directed_set_from_basis B y)).
  rewrite approximating_basis_lub in H.
  specialize (H H2).
  revert H.
  use factor_through_squash_hProp.
  intros ( i₂ & Hi₂ ).
  cbn in i₁, i₂, Hi₁, Hi₂.
  refine (hinhpr _).
  refine (pr1 i₁ ,, pr1 i₂ ,, pr2 i₁ ,, pr2 i₂ ,, _).
  use factor_through_squash.
  { apply isapropempty. }
  intros [ k [ Hik₁ Hik₂ ]].
  refine (Hdisj (B k) _).
  split.
  - apply (is_scott_open_upper_set S1 Hi₁).
    apply way_below_to_le.
    exact Hik₁.
  - apply (is_scott_open_upper_set S2 Hi₂).
    apply way_below_to_le.
    exact Hik₂.
Qed.

Definition to_hausdorff_separated_continuous_dcpo
           {X : dcpo}
           (B : dcpo_basis X)
           (x y : X)
  : (∃ (b₁ b₂ : B),
     B b₁ ≪ x
     ∧
     B b₂ ≪ y
     ∧
     ¬(∃ (t : B), B b₁ ≪ B t ∧ B b₂ ≪ B t))%logic
    →
    is_hausdorff_separated x y.
Proof.
  use factor_through_squash_hProp.
  intros ( b₁ & b₂ & p₁ & p₂ & p₃ ).
  refine (hinhpr _).
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - refine (_ ,, _).
    exact (upper_set_is_scott_open (continuous_struct_from_basis B) (B b₁)).
  - refine (_ ,, _).
    exact (upper_set_is_scott_open (continuous_struct_from_basis B) (B b₂)).
  - exact p₁.
  - exact p₂.
  - cbn -[way_below] ; intros z ( Hz₁ & Hz₂ ).
    refine (p₃ _).
    assert (H := basis_binary_interpolation B Hz₁ Hz₂).
    revert H.
    use factor_through_squash_hProp.
    intros ( i & r₁ & r₂ & r₃ ).
    exact (hinhpr (i ,, r₁ ,, r₂)).
Qed.

Definition hausdorff_separated_continuous_dcpo_weq
           {X : dcpo}
           (B : dcpo_basis X)
           (x y : X)
  : (is_hausdorff_separated x y
     ≃
     ∃ (b₁ b₂ : B),
     B b₁ ≪ x
     ∧
     B b₂ ≪ y
     ∧
     ¬(∃ (t : B), B b₁ ≪ B t ∧ B b₂ ≪ B t))%logic.
Proof.
  use logeqweq.
  - exact (from_hausdorff_separated_continuous_dcpo B x y).
  - exact (to_hausdorff_separated_continuous_dcpo B x y).
Defined.

(** * 5. Strongly maximal elements *)
Definition is_strongly_maximal
           {X : dcpo}
           (x : X)
  : hProp
  := (∀ (u v : X), u ≪ v ⇒ (u ≪ x ∨ is_hausdorff_separated v x))%logic.

Definition strongly_maximal
           (X : dcpo)
  : hSet
  := (∑ (x : X), hProp_to_hSet (is_strongly_maximal x))%set.

#[reversible=no] Coercion element_of_strongly_maximal
         {X : dcpo}
         (x : strongly_maximal X)
  : X
  := pr1 x.

Definition eq_strongly_maximal
           {X : dcpo}
           {x y : strongly_maximal X}
           (p : pr1 x = pr1 y)
  : x = y.
Proof.
  use subtypePath.
  {
    intro.
    apply propproperty.
  }
  exact p.
Qed.

(** * 6. Strongly maximal elements are sharp *)
Proposition is_sharp_is_strongly_maximal
            {X : dcpo}
            {x : X}
            (Hx : is_strongly_maximal x)
  : is_sharp x.
Proof.
  intros u v p.
  specialize (Hx u v p).
  revert Hx.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro H.
  induction H as [ q | q ].
  - exact (hinhpr (inl q)).
  - refine (hinhpr (inr _)).
    apply is_hausdorff_separated_not_le.
    exact q.
Qed.

(** * 7. The intrinsic apartness relation on strongly maximal elements *)
Proposition is_strongly_maximal_tight_apartness
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            {x y : X}
            (Hx : is_strongly_maximal x)
            (Hy : is_strongly_maximal y)
            (p : ¬(x # y))
  : x = y.
Proof.
  refine (is_sharp_tight_apartness CX _ _ p).
  - apply is_sharp_is_strongly_maximal.
    exact Hx.
  - apply is_sharp_is_strongly_maximal.
    exact Hy.
Qed.

Proposition is_strongly_maximal_cotransitive_apartness
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            {x y z : X}
            (Hz : is_strongly_maximal z)
            (p : x # y)
  : x # z ∨ y # z.
Proof.
  refine (is_sharp_cotransitive_apartness CX _ p).
  apply is_sharp_is_strongly_maximal.
  exact Hz.
Qed.

(** * 8. In a continuous DCPO, strongly maximal elements are maximal *)
Proposition is_maximal_is_strongly_maximal
            {X : dcpo}
            (CX : continuous_dcpo_struct X)
            {x : X}
            (Hx : is_strongly_maximal x)
  : is_maximal x.
Proof.
  intros y p.
  use (invmap (continuous_dcpo_struct_le_via_approximation CX y x)).
  intros z q.
  assert (H := Hx z y q).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro H.
  induction H as [ r | r ].
  - exact r.
  - apply fromempty.
    exact (is_hausdorff_separated_not_le (symm_is_hausdorff_separated r) p).
Qed.

Definition eq_strongly_maximal_via_le
           {X : dcpo}
           (CX : continuous_dcpo_struct X)
           {x y : strongly_maximal X}
           (p : x ⊑ y)
  : x = y.
Proof.
  use subtypePath.
  {
    intro.
    apply propproperty.
  }
  use antisymm_dcpo.
  - exact p.
  - exact (is_maximal_is_strongly_maximal CX (pr2 x) _ p).
Qed.

Definition eq_strongly_maximal_via_top
           {X : dcpo}
           (CX : continuous_dcpo_struct X)
           {x y : strongly_maximal X}
           (z : X)
           (p : x ⊑ z)
           (q : y ⊑ z)
  : x = y.
Proof.
  use subtypePath.
  {
    intro.
    apply propproperty.
  }
  transitivity z.
  - use antisymm_dcpo.
    + exact p.
    + exact (is_maximal_is_strongly_maximal CX (pr2 x) _ p).
  - refine (!_).
    use antisymm_dcpo.
    + exact q.
    + exact (is_maximal_is_strongly_maximal CX (pr2 y) _ q).
Qed.

(** * 9. A simplified strong maximality condition in a continuous DCPO,
      in terms of the basis *)

Lemma is_strongly_maximal_basis_1  {X : dcpo} (B : dcpo_basis X) (x : X) :
  (∀ (i j : B), B i ≪ B j ⇒ (B i ≪ x ∨ is_hausdorff_separated (B j) x))%logic →
  is_strongly_maximal x.
Proof.
  intros HB u v Huv.
  assert (Hb := basis_unary_interpolation B Huv).
  revert Hb.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intros [i [Hui Hiv]].
  assert (Hb := basis_unary_interpolation B Hiv).
  revert Hb.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intros [j [Hij Hjv]].
  specialize (HB _ _ Hij).
  revert HB.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intros [Hix | Hsep].
  { apply hinhpr. left.
    use (trans_way_below Hui Hix). }
  { apply hinhpr. right.
    use (is_hausdorff_separated_le _ _ _ _ Hsep).
    apply way_below_to_le, Hjv. }
Qed.

Lemma is_strongly_maximal_basis_2  {X : dcpo} (B : dcpo_basis X) (x : X) :
  is_strongly_maximal x →
  (∀ (i j : B), B i ≪ B j ⇒ (B i ≪ x ∨ is_hausdorff_separated (B j) x))%logic.
Proof.
  intros HX i j p.
  exact (HX (B i) (B j) p).
Qed.

Lemma is_strongly_maximal_basis {X : dcpo} (B : dcpo_basis X) (x : X) :
  (∀ (i j : B), B i ≪ B j ⇒ (B i ≪ x ∨ is_hausdorff_separated (B j) x))%logic ≃ is_strongly_maximal x.
Proof.
  use weqimplimpl.
  - apply is_strongly_maximal_basis_1.
  - apply is_strongly_maximal_basis_2.
  - apply propproperty.
  - apply propproperty.
Qed.

(** * 10. Apartness for strongly maximal elements is Hausdorff separatedness *)
Lemma strongly_maximal_apart
       {D : dcpo}
       (C : continuous_dcpo_struct D)
       {x y : D}
       (Hx : is_strongly_maximal x)
       (Hy : is_strongly_maximal y)
       (p : x # y)
  : is_hausdorff_separated x y.
Proof.
  revert p.
  use factor_through_squash_hProp.
  intros [Hxy | Hyx].
  - assert (Hb := continuous_not_specialization_weq C _ _ Hxy).
    revert Hb.
    use factor_through_squash_hProp.
    intros (b & Hbx & Hby).
    specialize (Hy b x Hbx).
    revert Hy.
    use factor_through_squash_hProp.
    intros [Hby' | Hxy' ].
    + apply fromempty.
      use (Hby _).
      exact (way_below_to_le Hby').
    + exact Hxy'.
  - assert (Hb := continuous_not_specialization_weq C _ _ Hyx).
    revert Hb.
    use factor_through_squash_hProp.
    intros (b & Hby & Hbx).
    specialize (Hx b y Hby).
    revert Hx.
    use factor_through_squash_hProp.
    intros [Hbx' | Hxy' ].
    + apply fromempty.
      use (Hbx _).
      exact (way_below_to_le Hbx').
    + apply symm_is_hausdorff_separated.
      exact Hxy'.
Qed.
