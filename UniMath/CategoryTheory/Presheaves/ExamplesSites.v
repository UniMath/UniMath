(**

 Examples of Grothendieck topologies and sites

 We discuss various examples of sites in this file. In particular, we show that every
 complete Heyting algebra induces a site and we discuss the dense topology. These
 examples are relevant for applications to logic.

 Content
 1. The indiscrete topology
 2. The discrete topology
 3. Every complete Heyting algebra induces a site
 4. The dense topology

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.OrderTheory.Lattice.DerivedLawsCompleteHeyting.

Local Open Scope cat.

(** * 1. The indiscrete topology *)
Definition indiscrete_topology
           (C : category)
  : grothendieck_topology C.
Proof.
  use make_grothendieck_topology.
  - exact (λ x ω, ∀ (y : C) (f : y --> x), ω y f).
  - exact (λ _ _ _, tt).
  - abstract
      (cbn ;
       intros x y f ω H z p ;
       apply H).
  - abstract
      (cbn ;
       intros x ω₁ ω₂ H p y f ;
       cbn in * ;
       specialize (p y f (H _ _) y (identity _)) ;
       rewrite id_left in p ;
       exact p).
Defined.

Definition indiscrete_site
           (C : category)
  : site.
Proof.
  use make_site.
  - exact C.
  - exact (indiscrete_topology C).
Defined.

(** * 2. The discrete topology *)
Definition discrete_topology
           (C : category)
  : grothendieck_topology C.
Proof.
  use make_grothendieck_topology.
  - exact (λ x ω, htrue).
  - abstract
      (intros ; cbn ;
       exact tt).
  - abstract
      (intros ; cbn ;
       exact tt).
  - abstract
      (intros ; cbn ;
       exact tt).
Defined.

Definition discrete_site
           (C : category)
  : site.
Proof.
  use make_site.
  - exact C.
  - exact (discrete_topology C).
Defined.

(** * 3. Every complete Heyting algebra induces a site *)
Local Open Scope heyting.

Proposition cha_eq_to_refl
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x = y)
  : x ≤ y.
Proof.
  induction p.
  apply cha_le_refl.
Qed.

Proposition cha_lub_monotone
            {H : complete_heyting_algebra}
            {X : UU}
            {f g : X → H}
            (p : ∏ (x : X), f x ≤ g x)
  : \/_{ x : X } f x ≤ \/_{ x : X} g x.
Proof.
  use cha_lub_le.
  intro i.
  use cha_le_lub.
  - exact i.
  - apply p.
Qed.

Section CHAToSite.
  Context (H : complete_heyting_algebra).

  Definition cha_to_poset
    : Poset.
  Proof.
    use make_Poset.
    - exact H.
    - use make_PartialOrder.
      + exact (λ (x y : H), x ≤ y).
      + repeat split.
        * intros x y z p q.
          exact (cha_le_trans p q).
        * intros x.
          exact (cha_le_refl x).
        * intros x y p q.
          exact (cha_le_antisymm p q).
  Defined.

  Let C : category := poset_to_poset_category cha_to_poset.

  Definition make_cha_sieve
             {x : C}
             (P : ∏ (y : C), y ≤ x → hProp)
             (Pc : ∏ (y₁ y₂ : C)
                     (p₁ : y₁ ≤ x)
                     (p₂ : y₂ ≤ y₁),
                   P y₁ p₁
                   → P y₂ (cha_le_trans p₂ p₁))
    : sieve x.
  Proof.
    use make_sieve.
    - exact P.
    - abstract
        (intros y₁ y₂ p₁ p₂ p₃ q r ;
         refine (transportf (P y₂) _ (Pc y₁ y₂ p₁ p₃ r)) ;
         apply propproperty).
  Defined.

  Definition cha_sieve_closed
             {x : C}
             (ω : sieve x)
             {y₁ y₂ : C}
             (p₁ : y₁ ≤ x)
             (p₂ : y₂ ≤ x)
             (p₃ : y₁ ≤ y₂)
             (q : ω y₂ p₂)
    : ω y₁ p₁.
  Proof.
    refine (#ω ω p₃ _ q).
    apply propproperty.
  Qed.

  Definition cha_sieve_fam
             {x : C}
             (ω : sieve x)
    : UU
    := ∑ (y : C) (p : y ≤ x), ω y p.

  Definition make_cha_sieve_fam
             {x : C}
             {ω : sieve x}
             (y : C)
             (p : y ≤ x)
             (q : ω y p)
    : cha_sieve_fam ω
    := y ,, p ,, q.

  Coercion cha_sieve_fam_el
           {x : C}
           {ω : sieve x}
           (y : cha_sieve_fam ω)
    : H
    := pr1 y.

  Definition cha_sieve_fam_le
             {x : C}
             {ω : sieve x}
             (y : cha_sieve_fam ω)
    : y ≤ x
    := pr12 y.

  Definition cha_sieve_fam_in
             {x : C}
             {ω : sieve x}
             (y : cha_sieve_fam ω)
    : ω _ (cha_sieve_fam_le y)
    := pr22 y.

  Definition cha_sieve_covers
             {x : C}
             (ω : sieve x)
    : hProp
    := x ≤ \/_{ j : cha_sieve_fam ω } j.

  Proposition cha_sieve_truth_covers
              (x : C)
    : cha_sieve_covers (truth_sieve x).
  Proof.
    unfold cha_sieve_covers.
    use cha_le_lub.
    - use make_cha_sieve_fam.
      + exact x.
      + apply cha_le_refl.
      + exact tt.
    - cbn.
      apply cha_le_refl.
  Qed.

  Proposition cha_sieve_stable_covers
              {x y : C}
              (p : x --> y)
              (ω : sieve y)
              (q : cha_sieve_covers ω)
    : cha_sieve_covers (p^* ω).
  Proof.
    unfold cha_sieve_covers.
    refine (cha_le_trans _ _).
    {
      use cha_eq_to_refl.
      exact (!(cha_min_le_eq_l p)).
    }
    refine (cha_le_trans _ _).
    {
      refine (cha_and_monotone_r _).
      exact q.
    }
    rewrite cha_frobenius.
    use cha_lub_le.
    intro i.
    use cha_le_lub.
    - use make_cha_sieve_fam.
      + exact (x ∧ i).
      + apply cha_min_le_l.
      + cbn.
        refine (cha_sieve_closed _ _ _ _ (cha_sieve_fam_in i)).
        apply cha_min_le_r.
    - cbn.
      apply cha_le_refl.
  Qed.

  Definition cha_trans_sieve
             {y : C}
             {ω₁ ω₂ : sieve y}
             (p : cha_sieve_covers ω₁)
             (q : ∏ (x : C) (h : x --> y), ω₁ x h → cha_sieve_covers (h ^* ω₂))
    : cha_sieve_covers ω₂.
  Proof.
    refine (cha_le_trans _ _).
    {
      exact p.
    }
    refine (cha_le_trans _ _).
    {
      refine (cha_lub_monotone _).
      intro x.
      exact (q _ _ (cha_sieve_fam_in x)).
    }
    cbn.
    use cha_lub_le.
    intro i.
    use cha_lub_le.
    intro j.
    cbn.
    use cha_le_lub.
    - use make_cha_sieve_fam.
      + exact (j : H).
      + refine (cha_le_trans (cha_sieve_fam_le j) _).
        exact (cha_sieve_fam_le i).
      + cbn.
        exact (cha_sieve_fam_in j).
    - cbn.
      apply cha_le_refl.
  Qed.

  Definition cha_to_grothendieck_topology
    : grothendieck_topology C.
  Proof.
    use make_grothendieck_topology.
    - exact (λ x ω, cha_sieve_covers ω).
    - exact cha_sieve_truth_covers.
    - exact (λ x y p ω, cha_sieve_stable_covers p ω).
    - exact (λ y ω₁ ω₂ p q, cha_trans_sieve p q).
  Defined.

  Definition cha_to_site
    : site.
  Proof.
    use make_site.
    - exact C.
    - exact cha_to_grothendieck_topology.
  Defined.
End CHAToSite.

(** * 4. The dense topology *)
Section DenseSite.
  Context (C : category).

  Definition dense_below
             (x : C)
             (ω : sieve x)
    : hProp
    := ∀ (y : C)
         (f : y --> x),
       ∃ (z : C)
         (g : z --> y),
       ω _ (g · f).

  Definition truth_sieve_dense_below
             (x : C)
    : dense_below x (truth_sieve x).
  Proof.
    intros y f.
    use hinhpr.
    refine (y ,, _).
    refine (identity _ ,, _) ; cbn.
    exact tt.
  Qed.

  Definition stable_dense_below
             {x y : C}
             (f : x --> y)
             (ω : sieve y)
             (p : dense_below y ω)
    : dense_below x (f ^* ω).
  Proof.
    intros z g.
    specialize (p z (g · f)).
    revert p.
    use factor_through_squash_hProp.
    intros (w & h & p).
    use hinhpr.
    simple refine (_ ,, _ ,, _).
    - exact w.
    - exact h.
    - cbn.
      rewrite assoc'.
      exact p.
  Qed.

  Definition trans_dens_below
             {y : C}
             (ω₁ ω₂ : sieve y)
             (p : dense_below y ω₁)
             (H : ∏ (x : C) (h : x --> y), ω₁ x h → dense_below x (h ^* ω₂))
    : dense_below y ω₂.
  Proof.
    intros z f.
    specialize (p z f).
    revert p.
    use factor_through_squash_hProp.
    intros (x & g & p).
    specialize (H x (g · f) p x (identity _)).
    revert H.
    use factor_through_squash_hProp.
    intros (w & h & q).
    use hinhpr.
    simple refine (w ,, _ ,, _).
    - exact (h · g).
    - cbn ; cbn in q.
      rewrite id_right in q.
      rewrite assoc'.
      exact q.
  Qed.

  Definition dense_topology
    : grothendieck_topology C.
  Proof.
    use make_grothendieck_topology.
    - exact dense_below.
    - exact truth_sieve_dense_below.
    - exact @stable_dense_below.
    - exact @trans_dens_below.
  Defined.

  Definition dense_site
    : site.
  Proof.
    use make_site.
    - exact C.
    - exact dense_topology.
  Defined.
End DenseSite.

Definition dense_set_poset
           (P : Poset)
  : site
  := dense_site (poset_to_poset_category P).
