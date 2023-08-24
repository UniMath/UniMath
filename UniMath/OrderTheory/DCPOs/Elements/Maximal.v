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
 4. Strongly maximal elements
 5. Strongly maximal elements are sharp
 6. The intrinsic apartness relation on strongly maximal elements
 7. In a continuous DCPO, strongly maximal elements are maximal

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Core.IntrinsicApartness.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.
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

(**
 1. Maximal elements
 *)
Definition is_maximal
           {X : dcpo}
           (x : X)
  : hProp
  := (∀ (y : X), x ⊑ y ⇒ y ⊑ x)%logic.

(**
 2. Hausdorff separated elements
 *)
Definition is_hausdorff_separated
           {X : dcpo}
           (x y : X)
  : hProp
  := ∃ (P₁ P₂ : scott_open_set X), P₁ x ∧ P₂ y ∧ are_disjoint P₁ P₂.

(**
 3. Properties of Hausdorff separated elements
 *)
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
End PropertiesHausdorffSeparated.

(**
 4. Strongly maximal elements
 *)
Definition is_strongly_maximal
           {X : dcpo}
           (x : X)
  : hProp
  := (∀ (u v : X), u ≪ v ⇒ (u ≪ x ∨ is_hausdorff_separated v x))%logic.

(**
 5. Strongly maximal elements are sharp
 *)
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

(**
 6. The intrinsic apartness relation on strongly maximal elements
 *)
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

(**
 7. In a continuous DCPO, strongly maximal elements are maximal
 *)
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
