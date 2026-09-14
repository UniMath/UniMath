(******************************************************************************************

 The existential quantifier

 In this file, we construct the conjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the existential quantifier, we reuse the existential
 quantifier of the first-order hyperdoctrine.

 Content
 1. The formula
 2. Introduction rule
 3. Elimination rule
 4. Stability under substitution

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMonomorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERConstantObjects.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Existential.
  Context {H : first_order_hyperdoctrine}
          {Γ A : partial_setoid H}
          (φ : per_subobject (prod_partial_setoid Γ A)).

  (** * 1. The formula *)
  Definition per_subobject_exists_form
    : form Γ
    := (∃h φ).

  Arguments per_subobject_exists_form /.

  Proposition per_subobject_exists_laws
    : per_subobject_laws per_subobject_exists_form.
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      refine (exists_elim (hyperdoctrine_hyp _) _).
      use weaken_right.
      hypersimplify.
      pose (γ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h A)))).
      pose (a := π₂ (tm_var ((𝟙 ×h Γ) ×h A))).
      fold γ a.
      refine (hyperdoctrine_cut _ _).
      {
        exact (per_subobject_def φ _ (hyperdoctrine_hyp _)).
      }
      refine (hyperdoctrine_cut _ _).
      {
        apply eq_in_prod_partial_setoid_l.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      hypersimplify.
      use hyp_sym.
      refine (exists_elim _ _).
      {
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      pose (a := π₂ (tm_var (((𝟙 ×h Γ) ×h Γ) ×h A))).
      pose (γ₁ := π₂ (π₁ (tm_var (((𝟙 ×h Γ) ×h Γ) ×h A)))).
      pose (γ₂ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ) ×h Γ) ×h A))))).
      use exists_intro.
      {
        exact a.
      }
      hypersimplify.
      fold a γ₁ γ₂.
      refine (per_subobject_eq _ _ (weaken_right (hyperdoctrine_hyp _) _)).
      use eq_in_prod_partial_setoid.
      + hypersimplify.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + hypersimplify.
        use weaken_right.
        refine (hyperdoctrine_cut _ _).
        {
          exact (per_subobject_def φ _ (hyperdoctrine_hyp _)).
        }
        refine (hyperdoctrine_cut _ _).
        {
          apply eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_exists
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact per_subobject_exists_form.
    - exact per_subobject_exists_laws.
  Defined.

  (** * 2. Introduction rule *)
  Proposition per_subobject_exists_intro
    : per_subobject_mor_law
        (id_partial_setoid_morphism (prod_partial_setoid Γ A))
        φ
        (per_subobject_subst
           (partial_setoid_comp_morphism
              (id_partial_setoid_morphism (prod_partial_setoid Γ A))
              (partial_setoid_pr1 Γ A))
           per_subobject_exists).
  Proof.
    use per_subobject_mor_law_over_id.
    cbn.
    use exists_intro.
    {
      exact (π₁ (tm_var _)).
    }
    hypersimplify.
    use conj_intro.
    - use exists_intro.
      {
        exact (tm_var _).
      }
      hypersimplify.
      repeat use conj_intro.
      + refine (per_subobject_def φ _ _).
        hypersimplify.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_cut (per_subobject_def φ (tm_var _) _) _).
        {
          hypersimplify.
          apply hyperdoctrine_hyp.
        }
        refine (hyperdoctrine_cut _ _).
        {
          exact (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)).
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_cut (per_subobject_def φ (tm_var _) _) _).
        {
          hypersimplify.
          apply hyperdoctrine_hyp.
        }
        refine (hyperdoctrine_cut _ _).
        {
          exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
    - use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      rewrite <- hyperdoctrine_pair_eta.
      hypersimplify.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 3. Elimination rule *)
  Proposition per_subobject_exists_elim
              (ψ : per_subobject Γ)
              (p : per_subobject_mor_law
                     (id_partial_setoid_morphism (prod_partial_setoid Γ A))
                     φ
                     (per_subobject_subst
                        (partial_setoid_comp_morphism
                           (id_partial_setoid_morphism _)
                           (partial_setoid_pr1 Γ A))
                        ψ))
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        per_subobject_exists
        ψ.
  Proof.
    use per_subobject_mor_law_over_id.
    cbn.
    refine (exists_elim (hyperdoctrine_hyp _) _).
    use weaken_right.
    refine (hyperdoctrine_cut _ _).
    {
      simple refine (per_subobject_mor_over_id p _).
      - exact (tm_var _).
      - hypersimplify.
        apply hyperdoctrine_hyp.
    }
    cbn.
    hypersimplify.
    refine (exists_elim (hyperdoctrine_hyp _) _).
    use weaken_right.
    refine (exists_elim _ _).
    {
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    rewrite conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    pose (Γ' := ((Γ ×h A) ×h Γ) ×h Γ ×h A).
    fold Γ'.
    pose (a₂ := π₂ (π₂ (tm_var Γ'))).
    pose (γ₃ := π₁ (π₂ (tm_var Γ'))).
    pose (γ₂ := π₂ (π₁ (tm_var Γ'))).
    pose (a₁ := π₂ (π₁ (π₁ (tm_var Γ')))).
    pose (γ₁ := π₁ (π₁ (π₁ (tm_var Γ')))).
    fold a₁ a₂ γ₁ γ₂ γ₃.
    rewrite (hyperdoctrine_pair_eta (π₂ (tm_var Γ'))).
    fold a₂ γ₃.
    cbn.
    rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var Γ')))).
    fold a₁ γ₁.
    refine (per_subobject_eq ψ _ _).
    - refine (partial_setoid_trans _ _ _).
      {
        do 2 use weaken_right.
        use weaken_left.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      use weaken_left.
      refine (hyperdoctrine_cut _ _).
      {
        apply eq_in_prod_partial_setoid_l.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      use partial_setoid_sym.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      apply hyperdoctrine_hyp.
  Qed.
End Existential.

Arguments per_subobject_exists_form /.

(** * 4. Stability under substitution *)
Proposition per_subobject_exists_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : partial_setoid H}
            (s : partial_setoid_morphism Γ₁ Γ₂)
            (φ : per_subobject (prod_partial_setoid Γ₂ A))
  : per_subobject_mor_law
      (id_partial_setoid_morphism Γ₁)
      (per_subobject_subst
         s
         (per_subobject_exists φ))
      (per_subobject_exists
         (per_subobject_subst
            (pair_partial_setoid_morphism
               (partial_setoid_comp_morphism (partial_setoid_pr1 Γ₁ A) s)
               (partial_setoid_comp_morphism
                  (partial_setoid_pr2 Γ₁ A)
                  (id_partial_setoid_morphism A)))
          φ)).
Proof.
  do 2 use forall_intro.
  use impl_intro.
  use weaken_right.
  use impl_intro.
  cbn.
  use hyp_sym.
  hypersimplify.
  refine (exists_elim _ _).
  {
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  rewrite conj_subst.
  use hyp_ltrans.
  use weaken_right.
  use hyp_rtrans.
  use hyp_sym.
  refine (exists_elim _ _).
  {
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  rewrite conj_subst.
  use hyp_ltrans.
  use weaken_right.
  hypersimplify.
  pose (Δ := (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h A).
  fold Δ.
  pose (a := π₂ (tm_var Δ)).
  pose (γ₁ := π₂ (π₁ (tm_var Δ))).
  pose (γ₂ := π₂ (π₁ (π₁ (tm_var Δ)))).
  pose (γ₃ := π₂ (π₁ (π₁ (π₁ (tm_var Δ))))).
  fold γ₁ γ₂ γ₃ a.
  use exists_intro.
  {
    exact a.
  }
  hypersimplify.
  use exists_intro.
  {
    exact ⟨ γ₁ , a ⟩.
  }
  hypersimplify.
  repeat use conj_intro.
  - use exists_intro.
    {
      exact γ₃.
    }
    hypersimplify.
    fold γ₂.
    repeat use conj_intro.
    + do 2 use weaken_left.
      apply partial_setoid_sym.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      refine (hyperdoctrine_cut _ _).
      {
        exact (per_subobject_def φ _ (hyperdoctrine_hyp _)).
      }
      refine (hyperdoctrine_cut _ _).
      {
        apply eq_in_prod_partial_setoid_r.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
    + use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
  - use exists_intro.
    {
      exact a.
    }
    hypersimplify.
    fold γ₂.
    repeat use conj_intro.
    + do 2 use weaken_left.
      refine (partial_setoid_refl_r _).
      apply hyperdoctrine_hyp.
    + use weaken_right.
      refine (hyperdoctrine_cut _ _).
      {
        exact (per_subobject_def φ _ (hyperdoctrine_hyp _)).
      }
      refine (hyperdoctrine_cut _ _).
      {
        apply eq_in_prod_partial_setoid_r.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      refine (hyperdoctrine_cut _ _).
      {
        exact (per_subobject_def φ _ (hyperdoctrine_hyp _)).
      }
      refine (hyperdoctrine_cut _ _).
      {
        apply eq_in_prod_partial_setoid_r.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
  - use weaken_right.
    apply hyperdoctrine_hyp.
Qed.
