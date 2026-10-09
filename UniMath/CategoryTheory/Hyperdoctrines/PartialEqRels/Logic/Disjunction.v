(******************************************************************************************

 Disjunction

 In this file, we construct the disjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the disjunction, we reuse the disjunction of the
 first-order hyperdoctrine.

 Content
 1. The formula
 2. Introduction rules
 3. Elimination rule
 4. Stability under substitution
 5. Fiberwise binary coproducts

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Disjunction.
  Context (H : first_order_hyperdoctrine).

  Section Disjunction.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

    (** * 1. The formula *)
    Proposition per_subobject_disj_laws
      : per_subobject_laws (ψ₁ ∨ ψ₂).
    Proof.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        hypersimplify.
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
        hypersimplify.
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

    (** * 2. Introduction rules *)
    Proposition per_subobject_disj_intro_left
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          ψ₁
          per_subobject_disj.
    Proof.
      use per_subobject_mor_law_over_id.
      cbn.
      use disj_intro_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition per_subobject_disj_intro_right
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          ψ₂
          per_subobject_disj.
    Proof.
      use per_subobject_mor_law_over_id.
      cbn.
      use disj_intro_right.
      apply hyperdoctrine_hyp.
    Qed.

    (** * 3. Elimination rule *)
    Context {χ : per_subobject Γ}
            (p : per_subobject_mor_law (id_partial_setoid_morphism Γ) ψ₁ χ)
            (q : per_subobject_mor_law (id_partial_setoid_morphism Γ) ψ₂ χ).

    Proposition per_subobject_disj_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          per_subobject_disj
          χ.
    Proof.
      use per_subobject_mor_law_over_id.
      cbn.
      refine (disj_elim (hyperdoctrine_hyp _) _ _).
      - use weaken_right.
        rewrite <- (hyperdoctrine_id_subst ψ₁).
        rewrite <- (hyperdoctrine_id_subst χ).
        use (per_subobject_mor_over_id p).
        apply hyperdoctrine_hyp.
      - use weaken_right.
        rewrite <- (hyperdoctrine_id_subst ψ₂).
        rewrite <- (hyperdoctrine_id_subst χ).
        use (per_subobject_mor_over_id q).
        apply hyperdoctrine_hyp.
    Qed.
  End Disjunction.

  (** * 4. Stability under substitution *)
  Proposition per_subobject_disj_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
              (ψ₁ ψ₂ : per_subobject Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_subst s (per_subobject_disj ψ₁ ψ₂))
        (per_subobject_disj (per_subobject_subst s ψ₁) (per_subobject_subst s ψ₂)).
  Proof.
    use per_subobject_mor_law_over_id.
    cbn.
    refine (exists_elim (hyperdoctrine_hyp _) _).
    use weaken_right.
    hypersimplify.
    use hyp_sym.
    refine (disj_elim _ _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_left.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_right.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 5. Fiberwise binary coproducts *)
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
End Disjunction.
