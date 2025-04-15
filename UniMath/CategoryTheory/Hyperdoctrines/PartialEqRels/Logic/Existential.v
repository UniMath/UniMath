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
 5. Dependent sums

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMonomorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERConstantObjects.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Existential.
  Context (H : first_order_hyperdoctrine).

  Section Existential.
    Context {A B : partial_setoid H}
            (φ : partial_setoid_morphism A B)
            (ψ : per_subobject A).

    (** * 1. The formula *)
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

    (** * 2. Introduction rule *)
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
      hypersimplify 0.
      rewrite partial_setoid_subst.
      simplify.
      simple refine (exists_elim (partial_setoid_mor_hom_exists φ _) _).
      - exact (π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      - use weaken_left.
        exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
      - hypersimplify 0.
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

    (** * 3. Elimination rule *)
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
      hypersimplify 0.
      rewrite partial_setoid_subst.
      simplify.
      use hyp_sym.
      simple refine (exists_elim (weaken_left (hyperdoctrine_hyp _) _) _).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify 0.
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
      hypersimplify 0.
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

  (** * 4. Stability under substitution *)
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
          hypersimplify 0.
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
          hypersimplify 0.
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
          hypersimplify 0.
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
          hypersimplify 0.
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
          hypersimplify 0.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          - exact q'.
          - refine (hyperdoctrine_cut q' _).
            unfold Δ, a₁, a₂, a₃, a₃', γ.
            hypersimplify 0.
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
          hypersimplify 0.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          - exact q'.
          - refine (hyperdoctrine_cut q' _).
            unfold Δ, a₁, a₂, a₃, a₃', γ.
            hypersimplify 0.
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
      hypersimplify 0.
      rewrite partial_setoid_subst.
      simplify.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify 0.
      rewrite !partial_setoid_subst.
      simplify.
      use hyp_rtrans.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify 0.
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
      - hypersimplify 0.
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
               hypersimplify 0.
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
               hypersimplify 0.
               rewrite partial_setoid_subst.
               simplify.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.
  End ExistentialSubst.

  (** * 5. Dependent sums *)
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
End Existential.
