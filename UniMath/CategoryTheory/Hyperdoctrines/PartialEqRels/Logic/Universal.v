(******************************************************************************************

 The universal quantifier

 In this file, we construct the conjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the universal quantifier, we reuse the universal
 quantifier of the first-order hyperdoctrine. To prove stability under substitution, we
 use that the Beck-Chevalley condition for left adjoints implies the Beck-Chevalley condition
 for right adjoints.

 Content
 1. The formula
 2. The elimination rule
 3. The introduction rule
 4. Dependent products of subobjects

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Existential.

Local Open Scope cat.
Local Open Scope hd.

Section Connectives.
  Context (H : first_order_hyperdoctrine).

  Section Universal.
    Context {A B : partial_setoid H}
            (φ : partial_setoid_morphism A B)
            (ψ : per_subobject A).

    (** * 1. The formula *)
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
      hypersimplify_form.
      use weaken_left.
      hypersimplify.
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
      hypersimplify_form.
      use weaken_right.
      hypersimplify.
      refine (hyperdoctrine_cut _ _).
      {
        exact (forall_elim (hyperdoctrine_hyp _) a).
      }
      hypersimplify.
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
      hypersimplify_form.
      hypersimplify.
      use conj_intro.
      - exact p.
      - hypersimplify.
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
        hypersimplify_form.
        rewrite partial_setoid_subst.
        use weaken_left.
        hypersimplify.
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use to_per_subobject_forall_form.
        + use weaken_left.
          exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
        + use forall_intro.
          hypersimplify_form.
          hypersimplify.
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

    (** * 2. The elimination rule *)
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
      hypersimplify_form.
      hypersimplify.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
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

    (** * 3. The introduction rule *)
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
      hypersimplify.
      use to_per_subobject_forall_form.
      - pose (b₁ := π₂ (π₁ (tm_var ((𝟙 ×h B) ×h B)))).
        pose (b₂ := π₂ (tm_var ((𝟙 ×h B) ×h B))).
        fold b₁ b₂.
        use weaken_left.
        exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
      - use forall_intro.
        use impl_intro.
        hypersimplify_form.
        hypersimplify.
        pose (b₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A))))).
        pose (b₂ := π₂ (π₁ (tm_var (((𝟙 ×h B) ×h B) ×h A)))).
        pose (a := π₂ (tm_var (((𝟙 ×h B) ×h B) ×h A))).
        fold a b₁ b₂.
        use (per_subobject_mor p).
        + exact a.
        + cbn.
          hypersimplify.
          use weaken_right.
          use (partial_setoid_mor_dom_defined φ a b₂).
          apply hyperdoctrine_hyp.
        + cbn.
          hypersimplify.
          use exists_intro.
          {
            exact b₁.
          }
          hypersimplify.
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

  (** * 4. Dependent products of subobjects *)
  Definition dependent_product_of_per_subobject
             {A B : category_of_partial_setoids H}
             (φ : partial_setoid_morphism A B)
    : dependent_product (disp_cat_per_subobject_cleaving H) φ.
  Proof.
    apply right_adjoint_weq_coreflections.
    intro ψ.
    use make_coreflection'.
    - exact (per_subobject_forall φ ψ).
    - exact (per_subobject_forall_elim φ ψ).
    - intro p.
      use make_coreflection_arrow.
      + exact (per_subobject_forall_intro φ _ (coreflection_data_arrow p)).
      + apply (@locally_prop_disp_cat_per_subobject H).
      + abstract (
          intros;
          apply proofirrelevance, (locally_prop_disp_cat_per_subobject B B)
        ).
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
