(*****************************************************************

 Directed sets

 To define DCPOs, we need a suitable notion of directed sets. In
 this file, we define these basic notions and give some elementary
 constructions of directed sets.

 Contents
 1. Directed sets in a poset
 2. Accessors and builders
 3. Precomposing a directed set with a monotone map
 4. The constant directed set
 5. The product of directed sets
 6. Directed sets indexed by the natural numbers

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.

Declare Scope dcpo.
Delimit Scope dcpo with dcpo.

(**
 1. Directed sets in a poset
 *)
Section Directed.
  Context {X : hSet}
          (PX : PartialOrder X)
          {I : UU}
          (D : I → X).

  Definition is_directed
    : hProp
    := ∥ I ∥ ∧ ∀ (i j : I), ∃ (k : I), PX (D i) (D k) × PX (D j) (D k).

  Definition is_directed_el
             (H : is_directed)
    : ∥ I ∥
    := pr1 H.

  Definition is_directed_top
             (H : is_directed)
             (i j : I)
    : ∃ (k : I), PX (D i) (D k) × PX (D j) (D k)
    := pr2 H i j.
End Directed.

Arguments is_directed_el {X PX I D} H.
Arguments is_directed_top {X PX I D} H i j.

Definition directed_set
           {X : hSet}
           (PX : PartialOrder X)
  : UU
  := ∑ (I : UU)
       (D : I → X),
     is_directed PX D.

(**
 2. Accessors and builders
 *)
#[reversible=no] Coercion directed_set_dom
         {X : hSet}
         {PX : PartialOrder X}
         (D : directed_set PX)
  : UU
  := pr1 D.

Definition directed_set_map
           {X : hSet}
           {PX : PartialOrder X}
           (D : directed_set PX)
  : directed_set_dom D → X
  := pr12 D.

Coercion directed_set_map : directed_set >-> Funclass.

Definition directed_set_is_directed
           {X : hSet}
           {PX : PartialOrder X}
           (D : directed_set PX)
  : is_directed PX D
  := pr22 D.

Definition directed_set_el
           {X : hSet}
           {PX : PartialOrder X}
           (D : directed_set PX)
  : ∥ D ∥
  := is_directed_el (directed_set_is_directed D).

Definition directed_set_top
           {X : hSet}
           {PX : PartialOrder X}
           (D : directed_set PX)
           (i j : D)
  : ∃ (k : D), PX (D i) (D k) × PX (D j) (D k)
  := is_directed_top (directed_set_is_directed D) i j.

Definition make_directed_set
           {X : hSet}
           (PX : PartialOrder X)
           (I : UU)
           (D : I → X)
           (HD : is_directed PX D)
  : directed_set PX
  := I ,, (D ,, HD).

(**
 3. Precomposing a directed set with a monotone map
 *)
Proposition is_directed_comp
            {X Y : hSet}
            {PX : PartialOrder X}
            {PY : PartialOrder Y}
            (f : X → Y)
            (Hf : is_monotone PX PY f)
            {I : UU}
            {D : I → X}
            (HD : is_directed PX D)
  : is_directed PY (λ i, f(D i)).
Proof.
  induction HD as [ H₁ H₂ ].
  split.
  - exact H₁.
  - clear H₁.
    intros i j.
    specialize (H₂ i j).
    revert H₂.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros kp.
    apply hinhpr.
    refine (pr1 kp ,, _ ,, _).
    + apply Hf.
      exact (pr12 kp).
    + apply Hf.
      exact (pr22 kp).
Qed.

Definition directed_set_comp
           {X Y : hSet}
           {PX : PartialOrder X}
           {PY : PartialOrder Y}
           (f : monotone_function PX PY)
           (D : directed_set PX)
  : directed_set PY.
Proof.
  use (make_directed_set _ D).
  - exact (λ i, f(D i)).
  - use (is_directed_comp f (pr2 f)).
    exact (directed_set_is_directed D).
Defined.

Notation "f '{{' D '}}'" := (directed_set_comp f D) (at level 30) : dcpo.

(**
 4. The constant directed set
 *)
Proposition is_directed_const
            {X : hSet}
            (PX : PartialOrder X)
            (x : X)
            (I : UU)
            (i : ∥ I ∥)
  : is_directed PX (λ _ : I, x).
Proof.
  split.
  - exact i.
  - intros i₁ i₂.
    apply hinhpr.
    exists i₁.
    split ; apply refl_PartialOrder.
Qed.

Definition const_directed_set
           {X : hSet}
           (PX : PartialOrder X)
           (x : X)
           (I : UU)
           (i : ∥ I ∥)
  : directed_set PX.
Proof.
  use (make_directed_set _ I).
  - exact (λ _, x).
  - exact (is_directed_const PX x I i).
Defined.

(**
 5. The product of directed sets
 *)
Proposition is_directed_prod
            {X Y : hSet}
            {PX : PartialOrder X}
            {PY : PartialOrder Y}
            (D₁ : directed_set PX)
            (D₂ : directed_set PY)
  : is_directed
      (prod_PartialOrder PX PY)
      (λ (xy : D₁ × D₂), D₁ (pr1 xy),, D₂ (pr2 xy)).
Proof.
  split.
  - assert (i₁ := directed_set_el D₁).
    assert (i₂ := directed_set_el D₂).
    apply hinhand; assumption.
  - intros ij₁ ij₂.
    induction ij₁ as [ i₁ j₁ ].
    induction ij₂ as [ i₂ j₂ ].
    assert (k₁ := directed_set_top D₁ i₁ i₂).
    assert (k₂ := directed_set_top D₂ j₁ j₂).
    simple refine (hinhuniv2 _ k₁ k₂).
    clear k₁ k₂.
    intros k₁ k₂.
    induction k₁ as [ k₁ [ H₁ H₂ ]].
    induction k₂ as [ k₂ [ H₃ H₄ ]].
    refine (hinhpr ((k₁ ,, k₂) ,, _)) ; cbn.
    split.
    + exact (H₁ ,, H₃).
    + exact (H₂ ,, H₄).
Qed.

Definition prod_directed_set
           {X Y : hSet}
           {PX : PartialOrder X}
           {PY : PartialOrder Y}
           (D₁ : directed_set PX)
           (D₂ : directed_set PY)
  : directed_set (prod_PartialOrder PX PY).
Proof.
  use make_directed_set.
  - exact (D₁ × D₂).
  - exact (λ xy, D₁ (pr1 xy) ,, D₂ (pr2 xy)).
  - exact (is_directed_prod D₁ D₂).
Defined.

(**
 6. Directed sets indexed by the natural numbers
 *)
Proposition is_directed_nat
            {X : hSet}
            (PX : PartialOrder X)
            (D : ℕ → X)
            (HD : ∏ (i j : ℕ), i ≤ j → PX (D i) (D j))
  : is_directed PX D.
Proof.
  split.
  - exact (hinhpr 0).
  - intros i₁ i₂.
    assert (p := istotalnatleh i₁ i₂).
    revert p.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro p.
    apply hinhpr.
    induction p as [ p | p ].
    + refine (i₂ ,, HD _ _ _ ,, HD _ _ _).
      * exact p.
      * apply isreflnatleh.
    + refine (i₁ ,, HD _ _ _ ,, HD _ _ _).
      * apply isreflnatleh.
      * exact p.
Qed.

Definition nat_directed_set_monotone
           {X : hSet}
           (PX : PartialOrder X)
           (D : ℕ → X)
           (HD : ∏ (i j : ℕ), i ≤ j → PX (D i) (D j))
  : directed_set PX
  := ℕ ,, D ,, is_directed_nat PX D HD.

Proposition nat_directed_set_help_monotone
            {X : hSet}
            (PX : PartialOrder X)
            (D : ℕ → X)
            (HD : ∏ (i : ℕ), PX (D i) (D (S i)))
            (i k : ℕ)
  : PX (D i) (D (i + k)).
Proof.
  induction k as [ | k IHk ].
  - rewrite natplusr0.
    apply refl_PartialOrder.
  - rewrite <- plus_n_Sm.
    refine (trans_PartialOrder PX IHk _).
    apply HD.
Qed.

Definition nat_directed_set
           {X : hSet}
           (PX : PartialOrder X)
           (D : ℕ → X)
           (HD : ∏ (i : ℕ), PX (D i) (D (S i)))
  : directed_set PX.
Proof.
  use (nat_directed_set_monotone PX D).
  abstract
    (intros i j p ;
     pose (k := nat_le_diff p) ;
     induction k as [ k q ] ;
     rewrite <- q ;
     use nat_directed_set_help_monotone ;
     exact HD).
Defined.
