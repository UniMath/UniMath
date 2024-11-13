(******************************************************************************************


 Content
 1. Truth formula
 2. Falsity formula
 3. Conjunction
 4. Disjunction
 5. Implication
 6. Existential quantification
 7. Universal quantification

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMonomorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERConstantObjects.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.InternalLogic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Connectives.
  Context (H : first_order_hyperdoctrine).

  (** * 1. Truth formula *)
  Proposition per_subobject_truth_laws
              (Γ : partial_setoid H)
    : per_subobject_laws (tm_var Γ ~ tm_var Γ).
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      rewrite partial_setoid_subst.
      simplify.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      rewrite !partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use partial_setoid_refl_r.
      {
        exact γ₁.
      }
      use weaken_left.
      apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_truth
             (Γ : partial_setoid H)
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact (tm_var _ ~ tm_var _).
    - exact (per_subobject_truth_laws Γ).
  Defined.

  Proposition per_subobject_truth_intro
              {Γ : partial_setoid H}
              (φ : per_subobject Γ)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        φ
        (per_subobject_truth Γ).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    rewrite !partial_setoid_subst.
    simplify.
    pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
    pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
    fold γ₁ γ₂.
    use partial_setoid_refl_r.
    {
      exact γ₁.
    }
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition per_subobject_truth_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_truth Γ₁)
        (per_subobject_subst s (per_subobject_truth Γ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    rewrite !partial_setoid_subst.
    simplify.
    pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁)))).
    pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁))).
    fold γ₁ γ₂.
    simple refine (exists_elim (partial_setoid_mor_hom_exists s _) _).
    - exact γ₂.
    - use weaken_left.
      use partial_setoid_refl_r.
      {
        exact γ₁.
      }
      apply hyperdoctrine_hyp.
    - unfold γ₁, γ₂ ; clear γ₁ γ₂.
      pose (γ₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
      pose (γ₂ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
      pose (γ₃ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
      rewrite exists_subst.
      use exists_intro.
      {
        exact γ₃.
      }
      rewrite partial_setoid_subst.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      fold γ₁ γ₂ γ₃.
      use conj_intro.
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use (partial_setoid_mor_cod_defined s).
        * exact γ₂.
        * apply hyperdoctrine_hyp.
  Qed.

  Definition fiberwise_terminal_per_subobject
    : fiberwise_terminal (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - exact per_subobject_truth.
    - intros Γ φ.
      exact (per_subobject_truth_intro φ).
    - intros Γ₁ Γ₂ s.
      exact (per_subobject_truth_subst s).
  Defined.

  (** * 2. Falsity formula *)
  Proposition per_subobject_false_laws
              (Γ : partial_setoid H)
    : per_subobject_laws (⊥ : form Γ).
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      simplify.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      do 2 use impl_intro.
      use weaken_right.
      use false_elim.
      simplify.
      apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_false
             (Γ : partial_setoid H)
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact ⊥.
    - exact (per_subobject_false_laws Γ).
  Defined.

  Proposition per_subobject_false_elim
              {Γ : partial_setoid H}
              (φ : per_subobject Γ)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        (per_subobject_false Γ)
        φ.
  Proof.
    do 2 use forall_intro.
    do 2 use impl_intro.
    use weaken_right.
    cbn.
    use false_elim.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition per_subobject_false_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_subst s (per_subobject_false Γ₂))
        (per_subobject_false Γ₁).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    use hyp_sym.
    rewrite !exists_subst.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    rewrite !conj_subst.
    use hyp_ltrans.
    use weaken_right.
    do 2 use weaken_right.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Definition fiberwise_initial_per_subobject
    : fiberwise_initial (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - exact per_subobject_false.
    - intros Γ φ.
      exact (per_subobject_false_elim φ).
    - intros Γ₁ Γ₂ s.
      exact (per_subobject_false_subst s).
  Defined.

  (** * 3. Conjunction *)
  Section Conjunction.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

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
    simplify_form.
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

  (** * 4. Disjunction *)
  Section Disjunction.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

    Proposition per_subobject_disj_laws
      : per_subobject_laws (ψ₁ ∨ ψ₂).
    Proof.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use (disj_elim (hyperdoctrine_hyp _)).
        + use weaken_right.
          use (per_subobject_def ψ₁).
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use (per_subobject_def ψ₂).
          apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use hyp_sym.
        simplify.
        pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
        pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
        fold γ₁ γ₂.
        use (disj_elim (weaken_left (hyperdoctrine_hyp _) _)).
        + use hyp_ltrans.
          use weaken_right.
          use disj_intro_left.
          use (per_subobject_eq ψ₁).
          * exact γ₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + use hyp_ltrans.
          use weaken_right.
          use disj_intro_right.
          use (per_subobject_eq ψ₂).
          * exact γ₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_disj
      : per_subobject Γ.
    Proof.
      use make_per_subobject.
      - exact (ψ₁ ∨ ψ₂).
      - exact per_subobject_disj_laws.
    Defined.

    Proposition per_subobject_disj_intro_left
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          ψ₁
          per_subobject_disj.
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
      use disj_intro_left.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Proposition per_subobject_disj_intro_right
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          ψ₂
          per_subobject_disj.
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
      use disj_intro_right.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Context {χ : per_subobject Γ}
            (p : per_subobject_mor_law (id_partial_setoid_morphism Γ) ψ₁ χ)
            (q : per_subobject_mor_law (id_partial_setoid_morphism Γ) ψ₂ χ).

    Proposition per_subobject_disj_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          per_subobject_disj
          χ.
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
      use hyp_sym.
      use (disj_elim (weaken_left (hyperdoctrine_hyp _) _)).
      - use hyp_ltrans.
        use weaken_right.
        use (per_subobject_mor p).
        + exact γ₁.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - use hyp_ltrans.
        use weaken_right.
        use (per_subobject_mor q).
        + exact γ₁.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.
  End Disjunction.

  Proposition per_subobject_disj_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
              (ψ₁ ψ₂ : per_subobject Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_subst s (per_subobject_disj ψ₁ ψ₂))
        (per_subobject_disj (per_subobject_subst s ψ₁) (per_subobject_subst s ψ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    rewrite partial_setoid_subst.
    rewrite !exists_subst.
    use hyp_sym.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    rewrite !conj_subst.
    use hyp_ltrans.
    use weaken_right.
    simplify_form.
    rewrite !partial_setoid_subst.
    simplify.
    pose (γ₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
    pose (γ₁' := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
    pose (γ₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
    fold γ₁ γ₁' γ₂.
    use hyp_rtrans.
    use hyp_sym.
    use (disj_elim (weaken_left (hyperdoctrine_hyp _) _)).
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_left.
      use exists_intro.
      + exact γ₂.
      + simplify.
        fold γ₁'.
        use conj_intro.
        * use weaken_left.
          use (partial_setoid_mor_eq_defined s).
          ** exact γ₁.
          ** exact γ₂.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_right.
      use exists_intro.
      + exact γ₂.
      + simplify.
        fold γ₁'.
        use conj_intro.
        * use weaken_left.
          use (partial_setoid_mor_eq_defined s).
          ** exact γ₁.
          ** exact γ₂.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
  Qed.

  Definition fiberwise_bincoproducts_per_subobject
    : fiberwise_bincoproducts (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_disj ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_disj_intro_left ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_disj_intro_right ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂ χ p q.
      exact (per_subobject_disj_elim ψ₁ ψ₂ p q).
    - intros Γ₁ Γ₂ s ψ₁ ψ₂.
      exact (per_subobject_disj_subst s ψ₁ ψ₂).
  Defined.

  (** * 5. Implication *)
  Section Implication.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

    Let ζ : form Γ := let γ := tm_var Γ in (ψ₁ ⇒ ψ₂) ∧ γ ~ γ.

    Proposition per_subobject_impl_laws
      : per_subobject_laws ζ.
    Proof.
      unfold ζ.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (γ := π₂ (tm_var (𝟙 ×h Γ))).
        fold γ.
        use weaken_right.
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
        pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
        fold γ₁ γ₂.
        use conj_intro.
        + use impl_intro.
          use per_subobject_eq.
          * exact γ₁.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          * use impl_elim.
            ** exact (ψ₁ [ γ₁ ]).
            ** use per_subobject_eq.
               *** exact γ₂.
               *** use partial_setoid_sym.
                   do 2 use weaken_left.
                   apply hyperdoctrine_hyp.
               *** use weaken_right.
                   apply hyperdoctrine_hyp.
            ** use weaken_left.
               use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
        + use weaken_left.
          use partial_setoid_refl_r.
          * exact γ₁.
          * apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_impl
      : per_subobject Γ.
    Proof.
      use make_per_subobject.
      - exact ζ.
      - exact per_subobject_impl_laws.
    Defined.

    Proposition per_subobject_impl_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          (per_subobject_conj ψ₁ per_subobject_impl)
          ψ₂.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold ζ.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - use impl_elim.
        + exact (ψ₁ [ γ₁ ]).
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
    Qed.

    Context {χ : per_subobject Γ}
            (p : per_subobject_mor_law
                   (id_partial_setoid_morphism Γ)
                   (per_subobject_conj ψ₁ χ)
                   ψ₂).

    Proposition per_subobject_impl_intro
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          χ
          per_subobject_impl.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold ζ.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use conj_intro.
      - use impl_intro.
        use (per_subobject_mor p).
        + exact γ₁.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + cbn.
          simplify.
          use conj_intro.
          * use per_subobject_eq.
            ** exact γ₂.
            ** use partial_setoid_sym.
               do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
      - use weaken_left.
        use partial_setoid_refl_r.
        + exact γ₁.
        + apply hyperdoctrine_hyp.
    Qed.
  End Implication.

  Proposition per_subobject_impl_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
              (ψ₁ ψ₂ : per_subobject Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_impl
           (per_subobject_subst s ψ₁)
           (per_subobject_subst s ψ₂))
        (per_subobject_subst
           s
           (per_subobject_impl ψ₁ ψ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use hyp_sym.
    cbn.
    simplify_form.
    rewrite !partial_setoid_subst.
    simplify.
    simple refine (exists_elim (partial_setoid_mor_hom_exists s _) _).
    - exact (π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁)))).
    - use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (γ₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
      pose (γ₁' := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
      pose (γ₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
      fold γ₁ γ₁' γ₂.
      use exists_intro.
      + exact γ₂.
      + simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        fold γ₁' γ₂.
        repeat (use conj_intro).
        * use hyp_ltrans.
          use weaken_right.
          use partial_setoid_mor_eq_defined.
          ** exact γ₁.
          ** exact γ₂.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_cod_defined s γ₁).
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use impl_intro.
          do 3 use hyp_ltrans.
          refine (weaken_cut _ _).
          {
            use (impl_elim _ (weaken_left (hyperdoctrine_hyp _) _)).
            use (exists_intro).
            {
              exact γ₂.
            }
            simplify.
            fold γ₁.
            do 3 use weaken_right.
            apply hyperdoctrine_hyp.
          }
          use hyp_ltrans.
          use weaken_right.
          use hyp_sym.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          unfold γ₁, γ₁', γ₂ ; clear γ₁ γ₁' γ₂.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (γ₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))))).
          pose (γ₁' := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
          pose (γ₂ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
          pose (γ₂' := π₂ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))).
          fold γ₁ γ₁' γ₂ γ₂'.
          use per_subobject_eq.
          ** exact γ₂'.
          ** use (partial_setoid_mor_unique_im s).
             *** exact γ₁.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 do 2 use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_right.
          use (partial_setoid_mor_cod_defined s).
          ** exact γ₁.
          ** apply hyperdoctrine_hyp.
  Qed.

  Definition fiberwise_exponentials_per_subobject
    : fiberwise_exponentials fiberwise_binproducts_per_subobject.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_impl ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_impl_elim ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂ χ p.
      exact (per_subobject_impl_intro ψ₁ ψ₂ p).
    - intros Γ₁ Γ₂ s ψ₁ ψ₂.
      exact (per_subobject_impl_subst s ψ₁ ψ₂).
  Defined.

  (** * 6. Existential quantification *)
  Section Existential.
    Context {A B : partial_setoid H}
            (φ : partial_setoid_morphism A B)
            (ψ : per_subobject A).

    Definition per_subobject_exists_form
      : form B
      := let γ₂ := π₁ (tm_var (B ×h A)) in
         let γ₁ := π₂ (tm_var (B ×h A)) in
         (∃h (φ [ ⟨ γ₁ , γ₂ ⟩ ] ∧ ψ [ γ₁ ])).

    Proposition per_subobject_exists_laws
      : per_subobject_laws per_subobject_exists_form.
    Proof.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        unfold per_subobject_exists_form.
        simplify.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        pose (a := π₂ (tm_var ((𝟙 ×h B) ×h A))).
        pose (b := π₂ (π₁ (tm_var ((𝟙 ×h B) ×h A)))).
        fold a b.
        use weaken_left.
        use (partial_setoid_mor_cod_defined φ a b).
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use hyp_sym.
        unfold per_subobject_exists_form.
        simplify.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        rewrite conj_subst.
        use hyp_ltrans.
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        pose (b₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A))))).
        pose (b₂ := π₂ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A)))).
        pose (a := π₂ (tm_var (((𝟙 ×h B) ×h B) ×h A))).
        fold b₁ b₂ a.
        use exists_intro.
        + exact a.
        + simplify.
          fold a b₁ b₂.
          use conj_intro.
          * use (partial_setoid_mor_eq_defined φ).
            ** exact a.
            ** exact b₁.
            ** use weaken_right.
               use weaken_left.
               use (partial_setoid_mor_dom_defined φ a b₁).
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_exists
      : per_subobject B.
    Proof.
      use make_per_subobject.
      - exact per_subobject_exists_form.
      - exact per_subobject_exists_laws.
    Defined.

    Proposition per_subobject_exists_intro
      : per_subobject_mor_law
          (id_partial_setoid_morphism A)
          ψ
          (per_subobject_subst φ per_subobject_exists).
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold per_subobject_exists_form.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      simple refine (exists_elim (partial_setoid_mor_hom_exists φ _) _).
      - exact (π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      - use weaken_left.
        exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
      - simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (a₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h B))))).
        pose (a₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h B)))).
        pose (b := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h B))).
        fold a₁ a₂ b.
        use exists_intro.
        {
          exact b.
        }
        simplify.
        fold a₂.
        use conj_intro.
        + use (partial_setoid_mor_eq_defined φ).
          ** exact a₁.
          ** exact b.
          ** do 2 use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             exact (partial_setoid_mor_cod_defined φ a₁ b (hyperdoctrine_hyp _)).
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        + use exists_intro.
          {
            exact a₁.
          }
          simplify.
          use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Context {χ : per_subobject B}
            (p : per_subobject_mor_law
                   (id_partial_setoid_morphism A)
                   ψ
                   (per_subobject_subst φ χ)).

    Proposition per_subobject_exists_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism B)
          per_subobject_exists
          χ.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      cbn ; unfold per_subobject_exists_form.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use hyp_sym.
      simple refine (exists_elim (weaken_left (hyperdoctrine_hyp _) _) _).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (b₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A))))).
      pose (b₂ := π₂ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A)))).
      pose (a := π₂ (tm_var (((𝟙 ×h B) ×h B) ×h A))).
      fold a b₁ b₂.
      pose (Δ := b₁ ~ b₂ ∧ φ [⟨ a, b₁ ⟩] ∧ ψ [a]).
      assert (Δ ⊢ (id_partial_setoid_morphism A) [⟨ a , a ⟩]) as r₁.
      {
        cbn.
        rewrite partial_setoid_subst.
        simplify.
        unfold Δ.
        use weaken_right.
        use weaken_left.
        use (partial_setoid_mor_dom_defined φ a b₁).
        apply hyperdoctrine_hyp.
      }
      assert (Δ ⊢ ψ [a]) as r₂.
      {
        unfold Δ.
        do 2 use weaken_right.
        apply hyperdoctrine_hyp.
      }
      pose (per_subobject_mor p r₁ r₂) as r₃.
      unfold per_subobject_subst in r₃.
      cbn in r₃.
      rewrite exists_subst in r₃.
      refine (exists_elim r₃ _).
      unfold Δ ; clear Δ r₁ r₂ r₃.
      unfold a, b₁, b₂ ; clear a b₁ b₂.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (b₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h B) ×h B) ×h A) ×h B)))))).
      pose (b₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h B) ×h B) ×h A) ×h B))))).
      pose (a := π₂ (π₁ (tm_var ((((𝟙 ×h B) ×h B) ×h A) ×h B)))).
      pose (b₃ := π₂ (tm_var ((((𝟙 ×h B) ×h B) ×h A) ×h B))).
      fold a b₁ b₂ b₃.
      use per_subobject_eq.
      - exact b₃.
      - use partial_setoid_trans.
        + exact b₁.
        + use (partial_setoid_mor_unique_im φ).
          * exact a.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
      - do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.
  End Existential.

  Section ExistentialSubst.
    Context {A₁ A₂ A₃ A₄ : partial_setoid H}
            {s₁ : partial_setoid_morphism A₂ A₁}
            {s₂ : partial_setoid_morphism A₃ A₁}
            {s₃ : partial_setoid_morphism A₄ A₃}
            {s₄ : partial_setoid_morphism A₄ A₂}
            (p : partial_setoid_comp_morphism s₄ s₁
                 =
                 partial_setoid_comp_morphism s₃ s₂)
            (Hp : isPullback (C := category_of_partial_setoids H) p)
            (φ : per_subobject A₂).

    Let P : Pullback (C := category_of_partial_setoids H) s₁ s₂
      := make_Pullback _ Hp.

    Section PullbackArrow.
      Let Γ : ty H := (((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂.
      Let a₃ : tm Γ A₃ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂))))).
      Let a₃' : tm Γ A₃ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂)))).
      Let a₁ : tm Γ A₁ := π₂ (π₁ (tm_var ((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂))).
      Let a₂ : tm Γ A₂ := π₂ (tm_var ((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂)).
      Let Δ : form Γ := (a₃ ~ a₃' ∧ s₂ [⟨ a₃, a₁ ⟩]) ∧ s₁ [⟨ a₂, a₁ ⟩] ∧ φ [a₂].

      Local Lemma per_subobject_exists_subst_def_lem_1
        : Δ ⊢ a₂ ~ a₂.
      Proof.
        unfold Δ.
        use weaken_right.
        use weaken_left.
        use (partial_setoid_mor_dom_defined s₁ a₂ a₁).
        apply hyperdoctrine_hyp.
      Qed.

      Local Lemma per_subobject_exists_subst_def_lem_2
        : Δ ⊢ a₃ ~ a₃.
      Proof.
        unfold Δ.
        use weaken_left.
        use weaken_right.
        use (partial_setoid_mor_dom_defined s₂ a₃ a₁).
        apply hyperdoctrine_hyp.
      Qed.

      Let f : partial_setoid_morphism (formula_to_partial_setoid H Δ) A₂
        := point_partial_setoid_morphism H Δ a₂ per_subobject_exists_subst_def_lem_1.
      Let g : partial_setoid_morphism (formula_to_partial_setoid H Δ) A₃
        := point_partial_setoid_morphism H Δ a₃ per_subobject_exists_subst_def_lem_2.

      Local Lemma per_subobject_exists_subst_fun_eq
        : partial_setoid_comp_morphism f s₁
          =
          partial_setoid_comp_morphism g s₂.
      Proof.
        use eq_partial_setoid_morphism.
        - cbn.
          use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          unfold Γ, Δ, a₁, a₂, a₃, a₃'.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (Γ' := (((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂) ×h A₁) ×h A₂).
          fold Γ'.
          pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))))).
          pose (x₂ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))).
          pose (x₃ := π₂ (π₁ (π₁ (π₁ (tm_var Γ'))))).
          pose (x₄ := π₂ (π₁ (π₁ (tm_var Γ')))).
          pose (x₅ := π₂ (π₁ (tm_var Γ'))).
          pose (x₆ := π₂ (tm_var Γ')).
          fold x₁ x₂ x₃ x₄ x₅ x₆.
          use exists_intro.
          {
            exact x₁.
          }
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          fold x₁ x₂ x₃ x₄ x₅ x₆.
          repeat use conj_intro.
          + do 4 use weaken_left.
            apply hyperdoctrine_hyp.
          + do 3 use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_left.
            use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
          + do 4 use weaken_left.
            exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
          + use partial_setoid_mor_eq_defined.
            * exact x₁.
            * exact x₃.
            * do 4 use weaken_left.
              exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
            * use (partial_setoid_mor_unique_im s₁).
              ** exact x₄.
              ** do 2 use weaken_left.
                 use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
              ** use partial_setoid_mor_eq_defined.
                 *** exact x₆.
                 *** exact x₅.
                 *** use weaken_left.
                     use weaken_right.
                     apply hyperdoctrine_hyp.
                 *** use weaken_right.
                     use (partial_setoid_mor_cod_defined s₁ x₆ x₅).
                     apply hyperdoctrine_hyp.
                 *** use weaken_right.
                     apply hyperdoctrine_hyp.
            * do 3 use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
        - cbn.
          use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          unfold Γ, Δ, a₁, a₂, a₃, a₃'.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (Γ' := (((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂) ×h A₁) ×h A₃).
          fold Γ'.
          pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))))).
          pose (x₂ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))).
          pose (x₃ := π₂ (π₁ (π₁ (π₁ (tm_var Γ'))))).
          pose (x₄ := π₂ (π₁ (π₁ (tm_var Γ')))).
          pose (x₅ := π₂ (π₁ (tm_var Γ'))).
          pose (x₆ := π₂ (tm_var Γ')).
          fold x₁ x₂ x₃ x₄ x₅ x₆.
          use exists_intro.
          {
            exact x₄.
          }
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          fold x₁ x₂ x₃ x₄ x₅ x₆.
          repeat use conj_intro.
          + do 4 use weaken_left.
            apply hyperdoctrine_hyp.
          + do 3 use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_left.
            use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_left.
            use weaken_right.
            use weaken_left.
            use (partial_setoid_mor_dom_defined s₁ x₄ x₃).
            apply hyperdoctrine_hyp.
          + use partial_setoid_mor_eq_defined.
            * exact x₄.
            * exact x₃.
            * do 2 use weaken_left.
              use weaken_right.
              use weaken_left.
              use (partial_setoid_mor_dom_defined s₁ x₄ x₃).
              apply hyperdoctrine_hyp.
            * use (partial_setoid_mor_unique_im s₂).
              ** exact x₁.
              ** do 3 use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
              ** use partial_setoid_mor_eq_defined.
                 *** exact x₆.
                 *** exact x₅.
                 *** use weaken_left.
                     use weaken_right.
                     apply hyperdoctrine_hyp.
                 *** use weaken_right.
                     use (partial_setoid_mor_cod_defined s₂ x₆ x₅).
                     apply hyperdoctrine_hyp.
                 *** use weaken_right.
                     apply hyperdoctrine_hyp.
            * do 2 use weaken_left.
              use weaken_right.
              use weaken_left.
              apply hyperdoctrine_hyp.
      Qed.

      Local Definition per_subobject_exists_subst_pb_fun
        : partial_setoid_morphism (formula_to_partial_setoid H Δ) A₄
        := PullbackArrow P _ _ _ per_subobject_exists_subst_fun_eq.

      Let h : partial_setoid_morphism (formula_to_partial_setoid H Δ) A₄
        := per_subobject_exists_subst_pb_fun.
      Let Γ' : ty H := Γ ×h A₄.
      Let γ : tm Γ' Γ := π₁ (tm_var Γ').
      Let b₃ : tm Γ' A₃ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))).
      Let b₃' : tm Γ' A₃ := π₂ (π₁ (π₁ (π₁ (tm_var Γ')))).
      Let b₁ : tm Γ' A₁ := π₂ (π₁ (π₁ (tm_var Γ'))).
      Let b₂ : tm Γ' A₂ := π₂ (π₁ (tm_var Γ')).
      Let b₄ : tm Γ' A₄ := π₂ (tm_var Γ').

      Context (Δ' : form Γ').

      Local Lemma per_subobject_exists_subst_pb_fun_proj1
                  (q : Δ' ⊢ h [ ⟨ γ , b₄ ⟩ ])
                  (q' : Δ' ⊢ Δ [ γ ])
        : Δ' ⊢ s₄ [ ⟨ b₄ , b₂ ⟩ ].
      Proof.
        assert (partial_setoid_comp_morphism h s₄ = f) as r.
        {
          exact (PullbackArrow_PullbackPr1 P _ _ _ per_subobject_exists_subst_fun_eq).
        }
        assert (Δ' ⊢ f [⟨ γ , b₂ ⟩]) as r'.
        {
          unfold f, a₂ ; cbn.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          - exact q'.
          - refine (hyperdoctrine_cut q' _).
            unfold Δ, a₁, a₂, a₃, a₃', γ.
            simplify_form.
            rewrite partial_setoid_subst.
            simplify.
            fold b₁ b₂ b₃ b₃'.
            use weaken_right.
            use weaken_left.
            use (partial_setoid_mor_dom_defined s₁ b₂ b₁).
            apply hyperdoctrine_hyp.
        }
        refine (exists_elim _ _).
        {
          refine (hyperdoctrine_cut (from_eq_partial_setoid_morphism_b r r') _).
          cbn.
          simplify.
          apply hyperdoctrine_hyp.
        }
        simplify.
        use partial_setoid_mor_eq_defined.
        - exact (π₂ (tm_var _)).
        - exact (b₂ [ π₁ (tm_var _) ]tm).
        - use (partial_setoid_mor_unique_im h).
          + exact (γ [π₁ (tm_var _) ]tm).
          + use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          + use weaken_left.
            refine (hyperdoctrine_cut
                      (hyperdoctrine_proof_subst _ q)
                      _).
            simplify.
            apply hyperdoctrine_hyp.
        - do 2 use weaken_right.
          use (partial_setoid_mor_cod_defined s₄ (π₂ (tm_var _)) _).
          apply hyperdoctrine_hyp.
        - do 2 use weaken_right.
          apply hyperdoctrine_hyp.
      Qed.

      Local Lemma per_subobject_exists_subst_pb_fun_proj2
                  (q : Δ' ⊢ h [ ⟨ γ , b₄ ⟩ ])
                  (q' : Δ' ⊢ Δ [ γ ])
        : Δ' ⊢ s₃ [ ⟨ b₄ , b₃ ⟩ ].
      Proof.
        assert (partial_setoid_comp_morphism h s₃ = g) as r.
        {
          exact (PullbackArrow_PullbackPr2 P _ _ _ per_subobject_exists_subst_fun_eq).
        }
        assert (Δ' ⊢ g [⟨ γ , b₃ ⟩]) as r'.
        {
          unfold g, a₃ ; cbn.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          - exact q'.
          - refine (hyperdoctrine_cut q' _).
            unfold Δ, a₁, a₂, a₃, a₃', γ.
            simplify_form.
            rewrite partial_setoid_subst.
            simplify.
            fold b₁ b₂ b₃ b₃'.
            use weaken_left.
            use weaken_right.
            use (partial_setoid_mor_dom_defined s₂ b₃ b₁).
            apply hyperdoctrine_hyp.
        }
        refine (exists_elim _ _).
        {
          refine (hyperdoctrine_cut (from_eq_partial_setoid_morphism_b r r') _).
          cbn.
          simplify.
          apply hyperdoctrine_hyp.
        }
        simplify.
        use partial_setoid_mor_eq_defined.
        - exact (π₂ (tm_var _)).
        - exact (b₃ [ π₁ (tm_var _) ]tm).
        - use (partial_setoid_mor_unique_im h).
          + exact (γ [π₁ (tm_var _) ]tm).
          + use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          + use weaken_left.
            refine (hyperdoctrine_cut
                      (hyperdoctrine_proof_subst _ q)
                      _).
            simplify.
            apply hyperdoctrine_hyp.
        - do 2 use weaken_right.
          use (partial_setoid_mor_cod_defined s₃ (π₂ (tm_var _)) _).
          apply hyperdoctrine_hyp.
        - do 2 use weaken_right.
          apply hyperdoctrine_hyp.
      Qed.
    End PullbackArrow.

    Proposition per_subobject_exists_subst
      : per_subobject_mor_law
          (id_partial_setoid_morphism A₃)
          (per_subobject_subst s₂ (per_subobject_exists s₁ φ))
          (per_subobject_exists s₃ (per_subobject_subst s₄ φ)).
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold per_subobject_exists_form ; cbn.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use hyp_rtrans.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (h := per_subobject_exists_subst_pb_fun).
      simple refine (exists_elim (partial_setoid_mor_hom_exists h _) _).
      - apply tm_var.
      - cbn.
        use eq_in_formula_to_partial_setoid.
        + apply hyperdoctrine_refl.
        + simplify.
          pose (Γ := (((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂).
          fold Γ.
          pose (a₃ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
          pose (a₃' := π₂ (π₁ (π₁ (tm_var Γ)))).
          pose (a₁ := π₂ (π₁ (tm_var Γ))).
          pose (a₂ := π₂ (tm_var Γ)).
          fold a₁ a₂ a₃ a₃'.
          apply hyperdoctrine_hyp.
      - simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (Γ := ((((𝟙 ×h A₃) ×h A₃) ×h A₁) ×h A₂) ×h A₄).
        fold Γ.
        pose (a₃ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (a₃' := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (a₁ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (a₂ := π₂ (π₁ (tm_var Γ))).
        pose (a₄ := π₂ (tm_var Γ)).
        fold a₁ a₂ a₃ a₃' a₄.
        use exists_intro.
        {
          exact a₄.
        }
        simplify.
        fold a₃'.
        use conj_intro.
        + use partial_setoid_mor_eq_defined.
          * exact a₄.
          * exact a₃.
          * use weaken_right.
            exact (partial_setoid_mor_cod_defined h _ _ (hyperdoctrine_hyp _)).
          * do 3 use weaken_left.
            apply hyperdoctrine_hyp.
          * use per_subobject_exists_subst_pb_fun_proj2.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               simplify_form.
               rewrite partial_setoid_subst.
               simplify.
               apply hyperdoctrine_hyp.
        + use exists_intro.
          {
            exact a₂.
          }
          simplify.
          use conj_intro.
          * use per_subobject_exists_subst_pb_fun_proj1.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               simplify_form.
               rewrite partial_setoid_subst.
               simplify.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.
  End ExistentialSubst.

  Definition dependent_sums_per_subobject
    : has_dependent_sums (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_has_dependent_sums_poset.
    - apply locally_prop_disp_cat_per_subobject.
    - intros A B φ ψ.
      exact (per_subobject_exists φ ψ).
    - intros A B φ ψ.
      exact (per_subobject_exists_intro φ ψ).
    - intros A B φ ψ χ p.
      exact (per_subobject_exists_elim φ ψ p).
    - intros A₁ A₂ A₃ A₄ s₁ s₂ s₃ s₄ p Hp φ.
      exact (per_subobject_exists_subst p Hp φ).
  Defined.

  (** * 7. Universal quantification *)
  Section Universal.
    Context {A B : partial_setoid H}
            (φ : partial_setoid_morphism A B)
            (ψ : per_subobject A).

    Definition per_subobject_forall_form
      : form B
      := let γ₂ := π₁ (tm_var (B ×h A)) in
         let γ₁ := π₂ (tm_var (B ×h A)) in
         (tm_var _ ~ tm_var _ ∧ ∀h (φ [ ⟨ γ₁ , γ₂ ⟩ ] ⇒ ψ [ γ₁ ])).

    Proposition per_subobject_forall_form_eq
                {Γ : ty H}
                {Δ : form Γ}
                (b : tm Γ B)
                (p : Δ  ⊢ per_subobject_forall_form [ b ])
      : Δ ⊢ b ~ b.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold per_subobject_forall_form.
      simplify_form.
      use weaken_left.
      rewrite partial_setoid_subst.
      simplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition per_subobject_forall_form_all
                {Γ : ty H}
                {Δ : form Γ}
                {a : tm Γ A}
                {b : tm Γ B}
                (p : Δ ⊢ per_subobject_forall_form [ b ])
                (q : Δ ⊢ φ [ ⟨ a , b ⟩ ])
      : Δ ⊢ ψ [ a ].
    Proof.
      use (impl_elim q).
      refine (hyperdoctrine_cut p _).
      unfold per_subobject_forall_form.
      simplify_form.
      use weaken_right.
      simplify.
      refine (hyperdoctrine_cut _ _).
      {
        exact (forall_elim (hyperdoctrine_hyp _) a).
      }
      simplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition to_per_subobject_forall_form
                {Γ : ty H}
                {Δ : form Γ}
                {b : tm Γ B}
                (p : Δ ⊢ b ~ b)
                (q : Δ ⊢ ∀h (φ [ ⟨ π₂ (tm_var _) , b [π₁ (tm_var _)]tm ⟩]
                             ⇒
                             ψ [π₂ (tm_var _)]))
      : Δ ⊢ per_subobject_forall_form [ b ].
    Proof.
      unfold per_subobject_forall_form.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use conj_intro.
      - exact p.
      - simplify.
        exact q.
    Qed.

    Proposition per_subobject_forall_laws
      : per_subobject_laws per_subobject_forall_form.
    Proof.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        unfold per_subobject_forall_form.
        pose (b := π₂ (tm_var (𝟙 ×h B))).
        fold b.
        simplify_form.
        rewrite partial_setoid_subst.
        use weaken_left.
        simplify.
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use to_per_subobject_forall_form.
        + use weaken_left.
          exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
        + use forall_intro.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (b₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A))))).
          pose (b₂ := π₂ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A)))).
          pose (a := π₂ (tm_var (((𝟙 ×h B) ×h B) ×h A))).
          fold a b₁ b₂.
          use impl_intro.
          use per_subobject_forall_form_all.
          * exact b₁.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          * use partial_setoid_mor_eq_defined.
            ** exact a.
            ** exact b₂.
            ** use weaken_right.
               use (partial_setoid_mor_dom_defined φ a b₂).
               apply hyperdoctrine_hyp.
            ** use partial_setoid_sym.
               do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_forall
      : per_subobject B.
    Proof.
      use make_per_subobject.
      - exact per_subobject_forall_form.
      - exact per_subobject_forall_laws.
    Defined.

    Proposition per_subobject_forall_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism A)
          (per_subobject_subst φ per_subobject_forall)
          ψ.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      rewrite !partial_setoid_subst.
      simplify.
      pose (a₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h B))))).
      pose (a₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h B)))).
      pose (b := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h B))).
      fold a₁ a₂ b.
      use per_subobject_forall_form_all.
      - exact b.
      - do 2 use weaken_right.
        apply hyperdoctrine_hyp.
      - use partial_setoid_mor_eq_defined.
        + exact a₁.
        + exact b.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          use (partial_setoid_mor_cod_defined φ a₁ b).
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
    Qed.

    Context {χ : per_subobject B}
            (p : per_subobject_mor_law
                   (id_partial_setoid_morphism A)
                   (per_subobject_subst φ χ)
                   ψ).

    Proposition per_subobject_forall_intro
      : per_subobject_mor_law
          (id_partial_setoid_morphism B)
          χ
          per_subobject_forall.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      use to_per_subobject_forall_form.
      - pose (b₁ := π₂ (π₁ (tm_var ((𝟙 ×h B) ×h B)))).
        pose (b₂ := π₂ (tm_var ((𝟙 ×h B) ×h B))).
        fold b₁ b₂.
        use weaken_left.
        exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
      - use forall_intro.
        use impl_intro.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (b₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A))))).
        pose (b₂ := π₂ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A)))).
        pose (a := π₂ (tm_var (((𝟙 ×h B) ×h B) ×h A))).
        fold a b₁ b₂.
        use (per_subobject_mor p).
        + exact a.
        + cbn.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_right.
          use (partial_setoid_mor_dom_defined φ a b₂).
          apply hyperdoctrine_hyp.
        + cbn.
          simplify.
          use exists_intro.
          {
            exact b₁.
          }
          simplify.
          use conj_intro.
          * use (partial_setoid_mor_eq_defined φ).
            ** exact a.
            ** exact b₂.
            ** use weaken_right.
               use (partial_setoid_mor_dom_defined φ a b₂).
               apply hyperdoctrine_hyp.
            ** use partial_setoid_sym.
               do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.
  End Universal.

  Definition dependent_product_of_per_subobject
             {A B : category_of_partial_setoids H}
             (φ : partial_setoid_morphism A B)
    : dependent_product (disp_cat_per_subobject_cleaving H) φ.
  Proof.
    use left_adjoint_from_partial.
    - exact (λ ψ, per_subobject_forall φ ψ).
    - exact (λ ψ, per_subobject_forall_elim φ ψ).
    - intros ψ χ p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros ζ₁ ζ₂ ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           apply locally_prop_disp_cat_per_subobject).
      + simple refine (_ ,, _).
        * exact (per_subobject_forall_intro φ ψ p).
        * apply (@locally_prop_disp_cat_per_subobject H).
  Defined.

  Definition dependent_products_per_subobject
    : has_dependent_products (disp_cat_per_subobject_cleaving H).
  Proof.
    simple refine (_ ,, _).
    - exact (λ A B φ, dependent_product_of_per_subobject φ).
    - intros A₁ A₂ A₃ A₄ s₁ s₂ s₃ s₄ p Hp.
      use right_from_left_beck_chevalley.
      + apply dependent_sums_per_subobject.
      + apply dependent_sums_per_subobject.
      + apply dependent_sums_per_subobject.
        use is_symmetric_isPullback.
        exact Hp.
  Defined.
End Connectives.
