(******************************************************************************************

 The conjunction of formulas of partial setoids

 In this file, we construct the conjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the conjunction, we reuse the conjunction of the
 first-order hyperdoctrine.

 Content
 1. The formula
 2. Elimination rules
 3. Introduction rule
 4. Stability under substitution
 5. Fiberwise binary products

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Conjunction.
  Context (H : first_order_hyperdoctrine).

  Section Conjunction.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

    (** * 1. The formula *)
    Proposition per_subobject_conj_laws
      : per_subobject_laws (ψ₁ ∧ ψ₂).
    Proof.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use weaken_right.
        use (per_subobject_def ψ₂).
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
        pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
        fold γ₁ γ₂.
        use conj_intro.
        + use (per_subobject_eq ψ₁).
          * exact γ₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
        + use (per_subobject_eq ψ₂).
          * exact γ₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_conj
      : per_subobject Γ.
    Proof.
      use make_per_subobject.
      - exact (ψ₁ ∧ ψ₂).
      - exact per_subobject_conj_laws.
    Defined.

    (** * 2. Elimination rules *)
    Proposition per_subobject_conj_elim_left
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          per_subobject_conj
          ψ₁.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    Qed.

    Proposition per_subobject_conj_elim_right
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          per_subobject_conj
          ψ₂.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    (** * 3. Introduction rule *)
    Context {χ : per_subobject Γ}
            (p : per_subobject_mor_law (id_partial_setoid_morphism Γ) χ ψ₁)
            (q : per_subobject_mor_law (id_partial_setoid_morphism Γ) χ ψ₂).

    Proposition per_subobject_conj_intro
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          χ
          per_subobject_conj.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use conj_intro.
      - use (per_subobject_mor p).
        + exact γ₁.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - use (per_subobject_mor q).
        + exact γ₁.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.
  End Conjunction.

  (** * 4. Stability under substitution *)
  Proposition per_subobject_conj_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
              (ψ₁ ψ₂ : per_subobject Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_conj
           (per_subobject_subst s ψ₁)
           (per_subobject_subst s ψ₂))
        (per_subobject_subst
           s
           (per_subobject_conj ψ₁ ψ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    rewrite partial_setoid_subst.
    rewrite conj_subst.
    rewrite !exists_subst.
    use hyp_sym.
    use hyp_ltrans.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    rewrite !conj_subst.
    use hyp_ltrans.
    use weaken_right.
    use hyp_ltrans.
    rewrite exists_subst.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    rewrite !conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify 0.
    rewrite !partial_setoid_subst.
    simplify.
    pose (γ₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))))).
    pose (γ₁' := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
    pose (γ₂ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
    pose (γ₂' := π₂ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))).
    use exists_intro.
    {
      exact γ₂.
    }
    simplify.
    fold γ₁ γ₁' γ₂ γ₂'.
    assert ((γ₁ ~ γ₁' ∧ s [⟨ γ₁, γ₂ ⟩] ∧ ψ₁ [γ₂]) ∧ s [⟨ γ₁, γ₂' ⟩] ∧ ψ₂ [γ₂'] ⊢ γ₂ ~ γ₂')
      as r.
    {
      use (partial_setoid_mor_unique_im s).
      - exact γ₁.
      - use weaken_left.
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      - use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    }
    repeat (use conj_intro).
    - use weaken_left.
      use (partial_setoid_mor_eq_defined s).
      + exact γ₁.
      + exact γ₂.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use weaken_left.
        exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - use weaken_left.
      do 2 use weaken_right.
      apply hyperdoctrine_hyp.
    - use per_subobject_eq.
      + exact γ₂'.
      + use partial_setoid_sym.
        exact r.
      + do 2 use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  (** * 5. Fiberwise binary products *)
  Definition fiberwise_binproducts_per_subobject
    : fiberwise_binproducts (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_conj ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_conj_elim_left ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_conj_elim_right ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂ χ p q.
      exact (per_subobject_conj_intro ψ₁ ψ₂ p q).
    - intros Γ₁ Γ₂ s ψ₁ ψ₂.
      exact (per_subobject_conj_subst s ψ₁ ψ₂).
  Defined.
End Conjunction.
