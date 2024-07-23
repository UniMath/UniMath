(******************************************************************************************


 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.

Local Open Scope cat.
Local Open Scope hd.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.

Section FormulaFunctor.
  Context (H : first_order_hyperdoctrine).

  Definition formula_to_per_form
             {A : ty H}
             (φ : form A)
    : form (A ×h A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Proposition formula_to_per_axioms
              {A : ty H}
              (φ : form A)
    : per_axioms (formula_to_per_form φ).
  Proof.
    unfold formula_to_per_form.
    split.
    - unfold per_symm_axiom.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + use weaken_left.
        use hyperdoctrine_eq_sym.
        apply hyperdoctrine_hyp.
      + use hyperdoctrine_eq_transportf.
        * exact x₁.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use conj_intro.
      + use hyperdoctrine_eq_trans.
        * exact x₂.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition formula_to_per
          {A : ty H}
          (φ : form A)
    : per A.
  Proof.
    use make_per.
    - exact (formula_to_per_form φ).
    - exact (formula_to_per_axioms φ).
  Defined.

  Definition formula_to_partial_setoid
             {A : ty H}
             (φ : form A)
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact A.
    - exact (formula_to_per φ).
  Defined.

  Proposition eq_in_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ≡ t₂)
              (q : Δ ⊢ φ [ t₁ ])
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use conj_intro.
    - exact p.
    - exact q.
  Qed.

  Proposition eq_from_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition prop_from_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ φ [ t₁ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use weaken_right.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition prop_from_formula_to_partial_setoid'
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ φ [ t₂ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use hyperdoctrine_eq_transportf.
    - exact t₁.
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition formula_to_partial_setoid_incl_form
             {A : ty H}
             (φ : form A)
    : form (formula_to_partial_setoid φ ×h eq_partial_setoid A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Proposition formula_to_partial_setoid_incl_laws
              {A : ty H}
              (φ : form A)
    : partial_setoid_morphism_laws (formula_to_partial_setoid_incl_form φ).
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_formula_to_partial_setoid.
      + use hyperdoctrine_refl.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_refl.
    - unfold partial_setoid_mor_eq_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A)))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A))))).
      pose (x₃ := π₂ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A)))).
      pose (x₄ := π₂ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃ x₄.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + use hyp_rtrans.
        use weaken_left.
        use hyperdoctrine_eq_trans.
        * exact x₁.
        * do 2 use weaken_left.
          use hyperdoctrine_eq_sym.
          use (eq_from_formula_to_partial_setoid φ).
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact x₃.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_left.
             use weaken_right.
             use from_eq_in_eq_partial_setoid.
             apply hyperdoctrine_hyp.
      + use hyperdoctrine_eq_transportf.
        * exact x₁.
        * do 2 use weaken_left.
          exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_eq_trans.
      + exact x₁.
      + use hyperdoctrine_eq_sym.
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        pose (x := π₂ (tm_var (𝟙 ×h A))).
        fold x.
        use conj_intro.
        * use (eq_from_formula_to_partial_setoid φ).
          apply hyperdoctrine_hyp.
        * exact (prop_from_formula_to_partial_setoid φ (hyperdoctrine_hyp _)).
  Qed.

  Definition formula_to_partial_setoid_incl
             {A : ty H}
             (φ : form A)
    : partial_setoid_morphism
        (formula_to_partial_setoid φ)
        (eq_partial_setoid A).
  Proof.
    use make_partial_setoid_morphism.
    - exact (formula_to_partial_setoid_incl_form φ).
    - exact (formula_to_partial_setoid_incl_laws φ).
  Defined.

  Proposition isMonic_formula_to_partial_setoid_incl_eq
              {A : ty H}
              (φ : form A)
              (X : partial_setoid H)
              {ψ₁ ψ₂ : partial_setoid_morphism X (formula_to_partial_setoid φ)}
              (p : partial_setoid_comp_morphism ψ₁ (formula_to_partial_setoid_incl φ)
                   =
                   partial_setoid_comp_morphism ψ₂ (formula_to_partial_setoid_incl φ))
    : ψ₁ ⊢ ψ₂.
  Proof.
    refine (hyperdoctrine_cut
              (@from_eq_partial_setoid_morphism_f
                 _ _ _ _ _
                 p
                 _
                 ψ₁
                 (π₁ (tm_var _)) (π₂ (tm_var _))
                 _)
              _).
    - cbn.
      unfold formula_to_partial_setoid_incl_form.
      simplify_form.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        use conj_intro.
        * rewrite <- hyperdoctrine_pair_eta.
          rewrite hyperdoctrine_id_subst.
          apply hyperdoctrine_hyp.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** use hyperdoctrine_cut.
             *** exact (ψ₁ [ ⟨ π₁ (tm_var _) , π₂ (tm_var _) ⟩ ]).
             *** rewrite <- (hyperdoctrine_pair_eta (tm_var _)).
                 rewrite hyperdoctrine_id_subst.
                 apply hyperdoctrine_hyp.
             *** refine (hyperdoctrine_cut
                           (partial_setoid_mor_cod_defined
                              ψ₁
                              (π₁ (tm_var _)) (π₂ (tm_var _))
                              (hyperdoctrine_hyp _))
                           _).
                 exact (prop_from_formula_to_partial_setoid φ (hyperdoctrine_hyp _)).
    - cbn.
      unfold formula_to_partial_setoid_incl_form.
      simplify_form.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify.
      use hyp_rtrans.
      use weaken_left.
      pose (x := π₁ (π₁ (tm_var ((X ×h A) ×h A)))).
      pose (a := π₂ (tm_var ((X ×h A) ×h A))).
      pose (a' := π₂ (π₁ (tm_var ((X ×h A) ×h A)))).
      fold x a a'.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h A) ×h A)))).
      fold x a'.
      use hyperdoctrine_eq_transportf.
      + exact ⟨ x , a ⟩.
      + use weaken_right.
        use hyperdoctrine_eq_pair_eq.
        * apply hyperdoctrine_refl.
        * apply hyperdoctrine_hyp.
      + use weaken_left.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition isMonic_formula_to_partial_setoid_incl
              {A : ty H}
              (φ : form A)
    : isMonic (C := category_of_partial_setoids H) (formula_to_partial_setoid_incl φ).
  Proof.
    intros X ψ₁ ψ₂ p.
    use eq_partial_setoid_morphism.
    - use isMonic_formula_to_partial_setoid_incl_eq.
      exact p.
    - use isMonic_formula_to_partial_setoid_incl_eq.
      exact (!p).
  Qed.

  Definition proof_to_partial_setoid_morphism_form
             {Γ₁ Γ₂ : ty H}
             {Δ : form Γ₁}
             {φ : form Γ₂}
             {s : tm Γ₁ Γ₂}
             (q : Δ ⊢ φ [ s ])
    : form (formula_to_partial_setoid Δ ×h formula_to_partial_setoid φ)
    := let x := π₁ (tm_var (Γ₁ ×h Γ₂)) in
       let y := π₂ (tm_var (Γ₁ ×h Γ₂)) in
       Δ [ x ] ∧ φ [ y ] ∧ y ≡ s [ x ]tm.

  Proposition proof_to_partial_setoid_morphism_laws
              {Γ₁ Γ₂ : ty H}
              {Δ : form Γ₁}
              {φ : form Γ₂}
              {s : tm Γ₁ Γ₂}
              (q : Δ ⊢ φ [ s ])
    : partial_setoid_morphism_laws (proof_to_partial_setoid_morphism_form q).
  Proof.
    unfold proof_to_partial_setoid_morphism_form.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + apply hyperdoctrine_refl.
      + use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + apply hyperdoctrine_refl.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))).
      fold x₁ x₂ y₁ y₂.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + do 2 use weaken_left.
        use hyperdoctrine_eq_transportf.
        * apply x₁.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use conj_intro.
        * use weaken_left.
          use weaken_right.
          use hyperdoctrine_eq_transportf.
          ** apply y₁.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact y₁.
          ** use hyperdoctrine_eq_sym.
             use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use hyperdoctrine_eq_trans.
             *** exact (s [ x₁ ]tm).
             *** do 3 use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use hyperdoctrine_subst_eq.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      cbn.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
      pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
      pose (y₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))).
      fold x y₁ y₂.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use conj_intro.
      + use hyperdoctrine_eq_trans.
        * exact (s [ x ]tm).
        * use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_sym.
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      cbn.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      + exact (s [ π₂ (tm_var (𝟙 ×h Γ₁)) ]tm).
      + simplify.
        pose (x := π₂ (tm_var (𝟙 ×h Γ₁))).
        fold x.
        use conj_intro.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use conj_intro.
          ** use weaken_right.
             refine (hyperdoctrine_cut (hyperdoctrine_proof_subst x q) _).
             simplify.
             apply hyperdoctrine_hyp.
          ** apply hyperdoctrine_refl.
  Qed.

  Definition proof_to_partial_setoid_morphism
             {Γ₁ Γ₂ : ty H}
             {Δ : form Γ₁}
             {φ : form Γ₂}
             {s : tm Γ₁ Γ₂}
             (q : Δ ⊢ φ [ s ])
    : partial_setoid_morphism (formula_to_partial_setoid Δ) (formula_to_partial_setoid φ).
  Proof.
    use make_partial_setoid_morphism.
    - exact (proof_to_partial_setoid_morphism_form q).
    - exact (proof_to_partial_setoid_morphism_laws q).
  Defined.

  Proposition proof_to_partial_setoid_morphism_eq
              {Γ₁ Γ₂ : ty H}
              {Δ : form Γ₁}
              {φ : form Γ₂}
              {s : tm Γ₁ Γ₂}
              (q : Δ ⊢ φ [ s ])
    : partial_setoid_comp_morphism
        (proof_to_partial_setoid_morphism q)
        (formula_to_partial_setoid_incl φ)
      =
      partial_setoid_comp_morphism
        (formula_to_partial_setoid_incl Δ)
        (term_partial_setoid_morphism s).
  Proof.
    use eq_partial_setoid_morphism.
    - use (exists_elim (hyperdoctrine_hyp _)).
      cbn.
      unfold proof_to_partial_setoid_morphism_form.
      unfold formula_to_partial_setoid_incl_form.
      use weaken_right.
      simplify_form.
      use exists_intro.
      + exact (π₁ (π₁ (tm_var _))).
      + simplify.
        pose (x := π₁ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂)))).
        pose (y₁ := π₂ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂)))).
        pose (y₂ := π₂ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂))).
        fold x y₁ y₂.
        use conj_intro.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** do 2 use weaken_left.
             apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact y₂.
          ** use hyperdoctrine_eq_sym.
             use weaken_left.
             do 2 use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
    - use (exists_elim (hyperdoctrine_hyp _)).
      cbn.
      unfold proof_to_partial_setoid_morphism_form.
      unfold formula_to_partial_setoid_incl_form.
      use weaken_right.
      simplify_form.
      use exists_intro.
      + exact (π₂ (π₁ (tm_var _))).
      + simplify.
        pose (x₁ := π₁ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁)))).
        pose (y := π₂ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁)))).
        pose (x₂ := π₂ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁))).
        fold x₁ x₂ y.
        assert ((x₁ ≡ x₂ ∧ Δ [x₁]) ∧ s [x₂ ]tm ≡ y ⊢ φ [y]) as r.
        {
          refine (weaken_cut
                    (weaken_left (weaken_right (hyperdoctrine_proof_subst x₁ q) _) _)
                    _).
          simplify.
          use hyperdoctrine_eq_transportf.
          * exact (s [ x₁ ]tm).
          * use weaken_left.
            refine (hyperdoctrine_eq_trans _ (weaken_right (hyperdoctrine_hyp _) _)).
            do 2 use weaken_left.
            use hyperdoctrine_subst_eq.
            use hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        }
        use conj_intro.
        * use conj_intro.
          ** use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** exact r.
             *** use hyperdoctrine_eq_trans.
                 **** exact (s [ x₂ ]tm).
                 **** use hyperdoctrine_eq_sym.
                      use weaken_right.
                      apply hyperdoctrine_hyp.
                 **** use hyperdoctrine_subst_eq.
                      use hyperdoctrine_eq_sym.
                      do 2 use weaken_left.
                      apply hyperdoctrine_hyp.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** exact r.
  Qed.

  Definition partial_setoids_disp_functor_data
    : disp_functor_data
        (functor_to_partial_setoids H)
        (hyperdoctrine_formula_disp_cat H)
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - simple refine (λ (A : ty H) (φ : form A), make_mono_cod_fib_ob _).
      + exact (formula_to_partial_setoid φ).
      + use make_Monic.
        * exact (formula_to_partial_setoid_incl φ).
        * exact (isMonic_formula_to_partial_setoid_incl φ).
    - refine (λ (Γ₁ Γ₂ : ty H)
                (Δ : form Γ₁)
                (φ : form Γ₂)
                (s : tm Γ₁ Γ₂)
                p, _).
      simple refine ((_ ,, _) ,, tt).
      + exact (proof_to_partial_setoid_morphism (from_disp_mor_hyperdoctrine _ p)).
      + apply proof_to_partial_setoid_morphism_eq.
  Defined.

  Definition partial_setoids_disp_functor
    : disp_functor
        (functor_to_partial_setoids H)
        (hyperdoctrine_formula_disp_cat H)
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact partial_setoids_disp_functor_data.
    - abstract
        (split ; intro ; intros ; apply locally_propositional_mono_cod_disp_cat).
  Defined.

  Definition partial_setoids_disp_functor_ff
    : disp_functor_ff partial_setoids_disp_functor.
  Proof.
    refine (λ (X Y : ty H) (φ : form X) (ψ : form Y) (s : tm X Y), _).
    use isweqimplimpl.
    - intro p.
      use to_disp_mor_hyperdoctrine.
      cbn in p.
      induction p as [ [ χ p ] t ].
      induction t.
      simple refine (hyperdoctrine_cut (from_eq_partial_setoid_morphism_f (!p) _) _).
      + apply tm_var.
      + exact s.
      + cbn.
        simplify.
        use exists_intro.
        * exact (tm_var _).
        * unfold formula_to_partial_setoid_incl_form.
          simplify.
          simplify_form.
          repeat (use conj_intro).
          ** apply hyperdoctrine_refl.
          ** apply hyperdoctrine_hyp.
          ** apply hyperdoctrine_refl.
      + cbn.
        simplify.
        use (exists_elim (hyperdoctrine_hyp _)).
        do 2 use weaken_right.
        unfold formula_to_partial_setoid_incl_form.
        simplify.
        use hyperdoctrine_eq_transportf.
        * exact (π₂ (tm_var (X ×h Y))).
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - use invproofirrelevance.
      intros ? ?.
      apply disp_mor_eq_hyperdoctrine.
    - apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition TODO { A : UU } : A.
  Admitted.

  Section EssentiallySurjective.
    Context {A : ty H}
            {X : partial_setoid H}
            (φ : partial_setoid_morphism X (eq_partial_setoid A))
            (Hφ : isMonic (C := category_of_partial_setoids H) φ).

    Definition partial_setoids_disp_functor_eso_form
      : form A
      := let a := π₁ (tm_var (A ×h X)) in
         let x := π₂ (tm_var (A ×h X)) in
         (∃h (φ [ ⟨ x , a ⟩ ])).

    Definition partial_setoids_disp_functor_eso_mor_form
      : form (formula_to_partial_setoid partial_setoids_disp_functor_eso_form ×h X)
      := let a := π₁ (tm_var (A ×h X)) in
         let x := π₂ (tm_var (A ×h X)) in
         φ [ ⟨ x , a ⟩ ].

    Proposition partial_setoids_disp_functor_eso_mor_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_mor_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_mor_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula ; cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + apply hyperdoctrine_refl.
        + use exists_intro.
          * exact (π₂ (tm_var _)).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_cod_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_eq_defined_law.
        cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        refine (partial_setoid_mor_eq_defined φ _ _ (weaken_right (hyperdoctrine_hyp _) _)).
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          unfold partial_setoid_formula ; cbn.
          unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
          simplify_form.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law.
        cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify. (* here monic is needed *)
        assert (⊤ ⊢ π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X))) ~ π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X)))) as h₁.
        admit.
        assert (⊤ ⊢ π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X)) ~ π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X))) as h₂.
        admit.
        pose (partial_setoid_morphism_from_terminal
                X
                (π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X))))
                h₁)
          as f₁.
        pose (partial_setoid_morphism_from_terminal
                X
                (π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X)))
                h₂)
          as f₂.
        (*
        assert (partial_setoid_comp_morphism f₁ φ = partial_setoid_comp_morphism f₂ φ).
        {
          use eq_partial_setoid_morphism ; cbn.
          - use (exists_elim (hyperdoctrine_hyp _)).
            use weaken_right.
            simplify_form.
            use exists_intro.
            * exact (π₂ (tm_var _)).
            * simplify_form.
              rewrite !partial_setoid_subst.
              simplify.
              admit.
          - use (exists_elim (hyperdoctrine_hyp _)).
            use weaken_right.
            simplify_form.
            use exists_intro.
            * exact (π₂ (tm_var _)).
            * simplify_form.
              rewrite !partial_setoid_subst.
              simplify.
              admit.

              rewrite partial_setoid_subst.
            use weak
        Check Hφ _ f₁ f₂.
         *)

        (*
          we should restrict `eq_partial_setoid` using a context delta
          this way we restrict the elements

          given `A : ty`
                `Δ : form A`
          look at
               `x₁ ≡ x₂ ∧ Δ [ x₁ ]

          then we can add the assumptions`
         *)

        partial_setoid_morphism_from_terminal
        apply TODO.
      - unfold partial_setoid_mor_hom_exists_law.
        cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form.
        unfold partial_setoids_disp_functor_eso_form.
        simplify.
        use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_mor
      : partial_setoid_morphism
          (formula_to_partial_setoid partial_setoids_disp_functor_eso_form)
          X.
    Proof.
      use make_partial_setoid_morphism.
      - exact partial_setoids_disp_functor_eso_mor_form.
      - exact partial_setoids_disp_functor_eso_mor_laws.
    Defined.

    Proposition partial_setoids_disp_functor_eso_mor_comm
      : partial_setoid_comp_morphism
          partial_setoids_disp_functor_eso_mor
          φ
        =
        partial_setoid_comp_morphism
          (formula_to_partial_setoid_incl partial_setoids_disp_functor_eso_form)
          (id_partial_setoid_morphism (eq_partial_setoid A)).
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_mor_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use exists_intro.
        + exact (π₁ (π₁ (tm_var _))).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          repeat (use conj_intro).
          * apply hyperdoctrine_refl.
          * use exists_intro.
            ** exact (π₂ (tm_var _)).
            ** simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
          * use (partial_setoid_mor_unique_im φ).
            ** exact (π₂ (tm_var ((A ×h A) ×h X))).
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_mor_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        use hyp_sym.
        use hyp_rtrans.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use (hyperdoctrine_eq_transportf _ _ (weaken_right (hyperdoctrine_hyp _) _)).
            use hyperdoctrine_eq_pair_eq.
            ** apply hyperdoctrine_refl.
            ** use weaken_left.
               refine (hyperdoctrine_eq_trans (weaken_right (hyperdoctrine_hyp _) _) _).
               use weaken_left.
               use from_eq_in_eq_partial_setoid.
               apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_inv_form
      : form (X ×h formula_to_partial_setoid partial_setoids_disp_functor_eso_form)
      := let x := π₁ (tm_var (X ×h A)) in
         let a := π₂ (tm_var (X ×h A)) in
         φ [ ⟨ x , a ⟩ ].

    Proposition partial_setoids_disp_functor_eso_inv_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_inv_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_inv_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_cod_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + use from_eq_in_eq_partial_setoid.
          exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
        + use exists_intro.
          * exact (π₂ (π₁ (tm_var _))).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_eq_defined_law.
        cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        use (partial_setoid_mor_eq_defined φ).
        + exact (π₂ (π₁ (π₁ (π₁ (tm_var _))))).
        + exact (π₂ (π₁ (tm_var _))).
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          use weaken_right.
          unfold partial_setoid_formula.
          cbn.
          unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
          rewrite conj_subst.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law.
        cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + use from_eq_in_eq_partial_setoid.
          use (partial_setoid_mor_unique_im φ).
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + use exists_intro.
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * simplify.
            use weaken_left.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law.
        cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        use (exists_elim (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
        simplify_form.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + cbn.
          simplify.
          use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_inv
      : partial_setoid_morphism
          X
          (formula_to_partial_setoid partial_setoids_disp_functor_eso_form).
    Proof.
      use make_partial_setoid_morphism.
      - exact partial_setoids_disp_functor_eso_inv_form.
      - exact partial_setoids_disp_functor_eso_inv_laws.
    Defined.

    Proposition partial_setoids_disp_functor_eso_inv_comm
      : partial_setoid_comp_morphism
          partial_setoids_disp_functor_eso_inv
          (formula_to_partial_setoid_incl partial_setoids_disp_functor_eso_form)
        =
        partial_setoid_comp_morphism φ (id_partial_setoid_morphism (eq_partial_setoid A)).
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_inv_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        use hyp_rtrans.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        use exists_intro.
        + exact (π₂ (π₁ (tm_var _))).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          * use eq_in_eq_partial_setoid.
            use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_inv_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          repeat (use conj_intro).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use from_eq_in_eq_partial_setoid.
            apply hyperdoctrine_hyp.
          * use exists_intro.
            ** exact (π₁ (π₁ (tm_var _))).
            ** simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
    Qed.
  End EssentiallySurjective.

  Definition partial_setoids_disp_functor_ess_split_surj
    : disp_functor_disp_ess_split_surj partial_setoids_disp_functor.
  Proof.
    refine (λ (A : ty H) f, _).
    induction f as [ [ X φ ] Hφ ].
    simple refine (_ ,, _).
    - exact (partial_setoids_disp_functor_eso_form φ).
    - simple refine (_ ,, _ ,, _ ,, _).
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_mor.
        * apply partial_setoids_disp_functor_eso_mor_comm.
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_inv.
        * apply partial_setoids_disp_functor_eso_inv_comm.
      + apply locally_propositional_mono_cod_disp_cat.
      + apply locally_propositional_mono_cod_disp_cat.
  Defined.
End FormulaFunctor.
