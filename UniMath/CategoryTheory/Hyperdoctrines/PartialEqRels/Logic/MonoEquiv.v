(******************************************************************************************

 Equivalence between subobjects and codomains

 We show construct a displayed equivalence between the displayed category of monomorphisms
 and of subobjects of partial setoids, as defined in `SubobjectDispCat.v`. This allows us
 to reason about the internal logic of partial setoids using the notion of subobject that
 we defined in `SubobjectDispCat`. This simplifies reasoning in the internal logic.

 In essence, the construction in this file is a more complicated but more general version
 of the construction in `PERMonomorphisms.v`. We reuse several lemmas from that file about
 monomorphisms.

 Content
 1. Subobjects to monomorphisms
 2. The action on morphisms
 3. The displayed functor
 4. Fully faithfulness
 5. Split essential surjectivity

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMonomorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section MonoSubobjectEquiv.
  Context (H : first_order_hyperdoctrine).

  (** * 1. Subobjects to monomorphisms *)
  Section SubobjectToMono.
    Context {X : partial_setoid H}
            (φ : per_subobject X).

    Let χ : form (X ×h X)
      := let x₁ := π₁ (tm_var (X ×h X)) in
         let x₂ := π₂ (tm_var (X ×h X)) in
         x₁ ~ x₂ ∧ φ [ x₁ ].

    Proposition subobject_to_per_axioms
      : per_axioms χ.
    Proof.
      unfold χ.
      split.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((𝟙 ×h X) ×h X))).
        fold x₁ x₂.
        use conj_intro.
        + use weaken_left.
          use partial_setoid_sym.
          apply hyperdoctrine_hyp.
        + use per_subobject_eq.
          * exact x₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
      - do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X))))).
        pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X)))).
        pose (x₃ := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h X))).
        fold x₁ x₂ x₃.
        use conj_intro.
        + use partial_setoid_trans.
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

    Definition subobject_to_per
      : per X.
    Proof.
      use make_per.
      - exact χ.
      - exact subobject_to_per_axioms.
    Defined.

    Definition subobject_to_partial_setoid
      : partial_setoid H.
    Proof.
      use make_partial_setoid.
      - exact X.
      - exact subobject_to_per.
    Defined.

    Proposition to_subobject_to_partial_setoid_eq
                {Γ : ty H}
                {x y : tm Γ subobject_to_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ (x : tm Γ X) ~ y)
                (q : Δ ⊢ φ [x])
      : Δ ⊢ x ~ y.
    Proof.
      unfold partial_setoid_formula ; cbn.
      unfold χ.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use conj_intro.
      - exact p.
      - exact q.
    Qed.

    Proposition from_subobject_to_partial_setoid_eq
                {Γ : ty H}
                {x y : tm Γ subobject_to_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ x ~ y)
      : Δ ⊢ (x : tm Γ X) ~ y.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn.
      unfold χ.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition from_subobject_to_partial_setoid_sub
                {Γ : ty H}
                {x y : tm Γ subobject_to_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ x ~ y)
      : Δ ⊢ φ [x].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn.
      unfold χ.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use weaken_right.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition subobject_to_partial_setoid_incl_laws
      : @partial_setoid_morphism_laws
           H
           subobject_to_partial_setoid
           X
           χ.
    Proof.
      unfold χ.
      repeat split.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        cbn.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((𝟙 ×h X) ×h X))).
        fold x₁ x₂.
        use to_subobject_to_partial_setoid_eq.
        + use weaken_left.
          exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((𝟙 ×h X) ×h X))).
        fold x₁ x₂.
        use weaken_left.
        exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
      - do 4 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h X) ×h X)))))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h X) ×h X))))).
        pose (x₃ := π₂ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h X) ×h X)))).
        pose (x₄ := π₂ (tm_var ((((𝟙 ×h X) ×h X) ×h X) ×h X))).
        fold x₁ x₂ x₃ x₄.
        use conj_intro.
        + use partial_setoid_trans.
          * exact x₃.
          * use partial_setoid_trans.
            ** exact x₁.
            ** use partial_setoid_sym.
               do 2 use weaken_left.
               use from_subobject_to_partial_setoid_eq.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          use per_subobject_eq.
          * exact x₁.
          * use from_subobject_to_partial_setoid_eq.
            apply hyperdoctrine_hyp.
          * use from_subobject_to_partial_setoid_sub.
            ** exact x₂.
            ** apply hyperdoctrine_hyp.
      - do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        cbn.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X))))).
        pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X)))).
        pose (x₃ := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h X))).
        fold x₁ x₂ x₃.
        use partial_setoid_trans.
        + exact x₁.
        + use partial_setoid_sym.
          do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - use forall_intro.
        use impl_intro.
        cbn.
        use weaken_right.
        pose (x := π₂ (tm_var (𝟙 ×h X))).
        fold x.
        use exists_intro.
        {
          exact x.
        }
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        use conj_intro.
        + use from_subobject_to_partial_setoid_eq.
          apply hyperdoctrine_hyp.
        + use from_subobject_to_partial_setoid_sub.
          * exact x.
          * apply hyperdoctrine_hyp.
    Qed.

    Definition subobject_to_partial_setoid_incl
      : partial_setoid_morphism
          subobject_to_partial_setoid
          X.
    Proof.
      use make_partial_setoid_morphism.
      - exact χ.
      - exact subobject_to_partial_setoid_incl_laws.
    Defined.

    Proposition isMonic_subobject_to_partial_setoid_incl
      : isMonic
          (C := category_of_partial_setoids H)
          subobject_to_partial_setoid_incl.
    Proof.
      intros W ψ₁ ψ₂ p.
      cbn in W, ψ₁, ψ₂, p.
      use eq_partial_setoid_morphism.
      - rewrite <- (hyperdoctrine_id_subst ψ₁).
        rewrite <- (hyperdoctrine_id_subst ψ₂).
        rewrite (hyperdoctrine_pair_eta (tm_var _)).
        cbn.
        pose (w := π₁ (tm_var (W ×h X))).
        pose (x := π₂ (tm_var (W ×h X))).
        fold w x.
        refine (hyperdoctrine_cut _ _).
        {
          apply (from_eq_partial_setoid_morphism_f
                   p
                   (Δ := ψ₁ [⟨ w , x ⟩])
                   (t₁ := w) (t₂ := x)).
          cbn.
          simplify_form.
          use exists_intro.
          {
            exact x.
          }
          simplify.
          use conj_intro.
          + apply hyperdoctrine_hyp.
          + use (partial_setoid_mor_cod_defined ψ₁ w x).
            apply hyperdoctrine_hyp.
        }
        cbn.
        unfold w, x ; clear w x.
        simplify_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X)))).
        pose (x₁ := π₂ (π₁ (tm_var ((W ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((W ×h X) ×h X))).
        fold w x₁ x₂.
        use (partial_setoid_mor_eq_defined ψ₂).
        + exact w.
        + exact x₂.
        + use weaken_left.
          use (partial_setoid_mor_dom_defined ψ₂ w x₂).
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
      - rewrite <- (hyperdoctrine_id_subst ψ₁).
        rewrite <- (hyperdoctrine_id_subst ψ₂).
        rewrite (hyperdoctrine_pair_eta (tm_var _)).
        cbn.
        pose (w := π₁ (tm_var (W ×h X))).
        pose (x := π₂ (tm_var (W ×h X))).
        fold w x.
        refine (hyperdoctrine_cut _ _).
        {
          apply (from_eq_partial_setoid_morphism_b
                   p
                   (Δ := ψ₂ [⟨ w , x ⟩])
                   (t₁ := w) (t₂ := x)).
          cbn.
          simplify_form.
          use exists_intro.
          {
            exact x.
          }
          simplify.
          use conj_intro.
          + apply hyperdoctrine_hyp.
          + use (partial_setoid_mor_cod_defined ψ₂ w x).
            apply hyperdoctrine_hyp.
        }
        cbn.
        unfold w, x ; clear w x.
        simplify_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X)))).
        pose (x₁ := π₂ (π₁ (tm_var ((W ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((W ×h X) ×h X))).
        fold w x₁ x₂.
        use (partial_setoid_mor_eq_defined ψ₁).
        + exact w.
        + exact x₂.
        + use weaken_left.
          use (partial_setoid_mor_dom_defined ψ₁ w x₂).
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
    Qed.
  End SubobjectToMono.

  (** * 2. The action on morphisms *)
  Section SubobjectMorToMono.
    Context {X Y : partial_setoid H}
            (ψ₁ : per_subobject X)
            (ψ₂ : per_subobject Y)
            (φ : partial_setoid_morphism X Y)
            (p : per_subobject_mor_law φ ψ₁ ψ₂).

    Let ξ : form (X ×h Y)
      := let x := π₁ (tm_var (X ×h Y)) in
         let y := π₂ (tm_var (X ×h Y)) in
         φ [ ⟨ x , y ⟩ ] ∧ ψ₁ [ x ] ∧ ψ₂ [ y ].

    Proposition subobject_to_partial_setoid_mor_laws
      : @partial_setoid_morphism_laws
           _
           (subobject_to_partial_setoid ψ₁)
           (subobject_to_partial_setoid ψ₂)
           ξ.
    Proof.
      unfold ξ.
      repeat split.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify ; cbn.
        pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
        fold x y.
        use to_subobject_to_partial_setoid_eq.
        + use weaken_left.
          use (partial_setoid_mor_dom_defined φ x y).
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify ; cbn.
        pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
        fold x y.
        use to_subobject_to_partial_setoid_eq.
        + use weaken_left.
          use (partial_setoid_mor_cod_defined φ x y).
          apply hyperdoctrine_hyp.
        + do 2  use weaken_right.
          apply hyperdoctrine_hyp.
      - do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify ; cbn.
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))).
        fold x₁ x₂ y₁ y₂.
        repeat use conj_intro.
        + use (partial_setoid_mor_eq_defined φ).
          * exact x₁.
          * exact y₁.
          * do 2 use weaken_left.
            use (from_subobject_to_partial_setoid_eq ψ₁).
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            use (from_subobject_to_partial_setoid_eq ψ₂).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
        + use per_subobject_eq.
          * exact x₁.
          * do 2 use weaken_left.
            use (from_subobject_to_partial_setoid_eq ψ₁).
            apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
        + use per_subobject_eq.
          * exact y₁.
          * use weaken_left.
            use weaken_right.
            use (from_subobject_to_partial_setoid_eq ψ₂).
            apply hyperdoctrine_hyp.
          * do 3 use weaken_right.
            apply hyperdoctrine_hyp.
      - do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify ; cbn.
        pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))).
        fold x y₁ y₂.
        use to_subobject_to_partial_setoid_eq.
        + use (partial_setoid_mor_unique_im φ).
          * exact x.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
        + use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
      - use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        refine (exists_elim (partial_setoid_mor_hom_exists φ _) _).
        + use (from_subobject_to_partial_setoid_eq ψ₁).
          apply hyperdoctrine_hyp.
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
          pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
          fold x y.
          use exists_intro.
          {
            exact y.
          }
          simplify ; cbn.
          fold x y.
          repeat use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use from_subobject_to_partial_setoid_sub.
            ** exact x.
            ** apply hyperdoctrine_hyp.
          * use (per_subobject_mor p).
            ** exact x.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               use (from_subobject_to_partial_setoid_sub ψ₁).
               *** exact x.
               *** apply hyperdoctrine_hyp.
    Qed.

    Definition subobject_to_partial_setoid_mor
      : partial_setoid_morphism
          (subobject_to_partial_setoid ψ₁)
          (subobject_to_partial_setoid ψ₂).
    Proof.
      use make_partial_setoid_morphism.
      - exact ξ.
      - exact subobject_to_partial_setoid_mor_laws.
    Defined.

    Proposition subobject_to_partial_setoid_mor_eq
      : partial_setoid_comp_morphism
          subobject_to_partial_setoid_mor
          (subobject_to_partial_setoid_incl ψ₂)
        =
        partial_setoid_comp_morphism
          (subobject_to_partial_setoid_incl ψ₁)
          φ.
    Proof.
      use eq_partial_setoid_morphism.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        cbn ; unfold ξ ; cbn.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y₁ := π₂ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var ((X ×h Y) ×h Y))).
        fold x y₁ y₂.
        use exists_intro.
        {
          exact x.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        fold x y₁ y₂.
        repeat use conj_intro.
        + do 2 use weaken_left.
          use (partial_setoid_mor_dom_defined φ x y₂).
          apply hyperdoctrine_hyp.
        + use weaken_left.
          use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use partial_setoid_mor_eq_defined.
          * exact x.
          * exact y₂.
          * do 2 use weaken_left.
            use (partial_setoid_mor_dom_defined φ x y₂).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        cbn ; unfold ξ ; cbn.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₁ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (x₂ := π₂ (tm_var ((X ×h Y) ×h X))).
        fold x₁ x₂ y.
        use exists_intro.
        {
          exact y.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        fold x₁ x₂ y.
        repeat use conj_intro.
        + use partial_setoid_mor_eq_defined.
          * exact x₂.
          * exact y.
          * do 2 use weaken_left.
            use partial_setoid_sym.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use (partial_setoid_mor_cod_defined φ x₂ y).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + use (per_subobject_mor p).
          * exact x₂.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use per_subobject_eq.
            ** exact x₁.
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
        + use weaken_right.
          use (partial_setoid_mor_cod_defined φ x₂ y).
          apply hyperdoctrine_hyp.
        + use (per_subobject_mor p).
          * exact x₂.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use per_subobject_eq.
            ** exact x₁.
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.
  End SubobjectMorToMono.

  (** * 3. The displayed functor *)
  Definition per_subobject_disp_functor_data
    : disp_functor_data
        (functor_identity _)
        (disp_cat_per_subobject H)
        (disp_mono_codomain (category_of_partial_setoids H)).
  Proof.
    simple refine (_ ,, _).
    - refine (λ (X : partial_setoid H)
                (φ : per_subobject X),
              (subobject_to_partial_setoid φ ,, subobject_to_partial_setoid_incl φ) ,, _).
      apply isMonic_subobject_to_partial_setoid_incl.
    - intros X Y ψ₁ ψ₂ φ p.
      refine ((subobject_to_partial_setoid_mor ψ₁ ψ₂ φ p ,, _) ,, tt).
      apply subobject_to_partial_setoid_mor_eq.
  Defined.

  Definition per_subobject_disp_functor
    : disp_functor
        (functor_identity _)
        (disp_cat_per_subobject H)
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact per_subobject_disp_functor_data.
    - abstract
        (split ; intro ; intros ; apply locally_propositional_mono_cod_disp_cat).
  Defined.

  (** * 4. Fully faithfulness *)
  Definition partial_setoids_disp_functor_ff
    : disp_functor_ff per_subobject_disp_functor.
  Proof.
    refine (λ (X Y : partial_setoid H)
              (ψ₁ : per_subobject X) (ψ₂ : per_subobject Y)
              (φ : partial_setoid_morphism X Y), _).
    use isweqimplimpl.
    - intro p.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
      fold x y.
      cbn in p.
      induction p as [ p t ].
      induction t.
      induction p as [ χ p ].
      simple refine (hyperdoctrine_cut (from_eq_partial_setoid_morphism_f (!p) _) _).
      + exact x.
      + exact y.
      + cbn.
        rewrite exists_subst.
        use exists_intro.
        {
          exact x.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        repeat use conj_intro.
        * use weaken_left.
          use (partial_setoid_mor_dom_defined φ x y).
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + cbn.
        unfold x, y ; clear x y.
        rewrite exists_subst.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))).
        fold x y₁ y₂.
        use per_subobject_eq.
        * exact y₂.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - use invproofirrelevance.
      intros ? ?.
      apply disp_mor_eq_hyperdoctrine.
    - apply locally_propositional_mono_cod_disp_cat.
  Qed.

  (** * 5. Split essential surjectivity *)
  Section Eso.
    Context {X Y : partial_setoid H}
            (φ : partial_setoid_morphism Y X)
            (Hφ : isMonic (C := category_of_partial_setoids H) φ).

    Let ζ : form X
      := let x := π₁ (tm_var (X ×h Y)) in
         let y := π₂ (tm_var (X ×h Y)) in
         (∃h (φ [ ⟨ y , x ⟩ ])).

    Proposition monic_to_per_subobject_laws
      : per_subobject_laws ζ.
    Proof.
      unfold ζ.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
        fold x y.
        use (partial_setoid_mor_cod_defined φ y x).
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use hyp_sym.
        simplify.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        rewrite conj_subst.
        use hyp_ltrans.
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y))))).
        pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h Y))).
        fold x₁ x₂ y.
        use exists_intro.
        {
          exact y.
        }
        simplify.
        fold x₂.
        use partial_setoid_mor_eq_defined.
        + exact y.
        + exact x₁.
        + use weaken_right.
          use (partial_setoid_mor_dom_defined φ y x₁).
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.

    Definition monic_to_per_subobject
      : per_subobject X.
    Proof.
      use make_per_subobject.
      - exact ζ.
      - exact monic_to_per_subobject_laws.
    Defined.

    Let ξ₁ : form (subobject_to_partial_setoid monic_to_per_subobject ×h Y)
      := let x := π₁ (tm_var (X ×h Y)) in
         let y := π₂ (tm_var (X ×h Y)) in
         φ [ ⟨ y , x ⟩ ].

    Proposition monic_to_per_subobject_mor_laws
      : partial_setoid_morphism_laws ξ₁.
    Proof.
      unfold ξ₁.
      repeat split.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify ; cbn.
        pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
        fold x y.
        use to_subobject_to_partial_setoid_eq.
        + use (partial_setoid_mor_cod_defined φ y x).
          apply hyperdoctrine_hyp.
        + cbn ; unfold ζ.
          rewrite exists_subst.
          use exists_intro.
          {
            exact y.
          }
          simplify.
          apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify ; cbn.
        pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
        fold x y.
        use (partial_setoid_mor_dom_defined φ y x).
        apply hyperdoctrine_hyp.
      - do 4 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))).
        fold x₁ x₂ y₁ y₂.
        use partial_setoid_mor_eq_defined.
        + exact y₁.
        + exact x₁.
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          use (from_subobject_to_partial_setoid_eq).
          * apply monic_to_per_subobject.
          * apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - do 3 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))).
        fold x y₁ y₂.
        use (partial_setoid_mono_eq φ Hφ).
        + exact x.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        unfold partial_setoid_formula; cbn.
        unfold ζ.
        simplify.
        use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Definition monic_to_per_subobject_mor
      : partial_setoid_morphism
          (subobject_to_partial_setoid monic_to_per_subobject)
          Y.
    Proof.
      use make_partial_setoid_morphism.
      - exact ξ₁.
      - exact monic_to_per_subobject_mor_laws.
    Defined.

    Proposition monic_to_per_subobject_mor_eq
      : partial_setoid_comp_morphism
          monic_to_per_subobject_mor
          φ
        =
        partial_setoid_comp_morphism
          (subobject_to_partial_setoid_incl monic_to_per_subobject)
          (id_partial_setoid_morphism X).
    Proof.
      use eq_partial_setoid_morphism.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right ; cbn.
        unfold ξ₁.
        simplify.
        pose (x₁ := π₁ (π₁ (tm_var ((X ×h X) ×h Y)))).
        pose (x₂ := π₂ (π₁ (tm_var ((X ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((X ×h X) ×h Y))).
        fold x₁ x₂ y.
        use exists_intro.
        + exact x₁.
        + unfold ζ.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          fold x₁ x₂.
          repeat use conj_intro.
          * use weaken_left.
            use (partial_setoid_mor_cod_defined φ y x₁).
            apply hyperdoctrine_hyp.
          * use exists_intro.
            {
              exact y.
            }
            simplify.
            fold x₁.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * use (partial_setoid_mor_unique_im φ).
            ** exact y.
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right ; cbn.
        unfold ζ.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use hyp_sym.
        use hyp_rtrans.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        rewrite conj_subst.
        use hyp_ltrans.
        use weaken_right.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₁ (π₁ (π₁ (tm_var (((X ×h X) ×h X) ×h Y))))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var (((X ×h X) ×h X) ×h Y))))).
        pose (x₃ := π₂ (π₁ (tm_var (((X ×h X) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((X ×h X) ×h X) ×h Y))).
        fold x₁ x₂ x₃ y.
        use exists_intro.
        + exact y.
        + unfold ξ₁.
          simplify.
          fold x₁ x₂.
          use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use partial_setoid_mor_eq_defined.
            ** exact y.
            ** exact x₁.
            ** use weaken_right.
               use (partial_setoid_mor_dom_defined φ y x₁).
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               use partial_setoid_trans.
               *** exact x₃.
               *** use weaken_right.
                   apply hyperdoctrine_hyp.
               *** use weaken_left.
                   apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.

    Let ξ₂ : form (Y ×h subobject_to_partial_setoid monic_to_per_subobject)
      := let y := π₁ (tm_var (Y ×h X)) in
         let x := π₂ (tm_var (Y ×h X)) in
         φ [ ⟨ y , x ⟩ ].

    Proposition monic_to_per_subobject_inv_laws
      : partial_setoid_morphism_laws ξ₂.
    Proof.
      unfold ξ₂.
      repeat split.
      - do 2 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        simplify.
        pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h X)))).
        pose (x := π₂ (tm_var ((𝟙 ×h Y) ×h X))).
        fold x y.
        use (partial_setoid_mor_dom_defined φ y x).
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        simplify.
        pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h X)))).
        pose (x := π₂ (tm_var ((𝟙 ×h Y) ×h X))).
        fold x y.
        use to_subobject_to_partial_setoid_eq.
        + use (partial_setoid_mor_cod_defined φ y x).
          apply hyperdoctrine_hyp.
        + cbn ; unfold ζ.
          simplify.
          use exists_intro.
          {
            exact y.
          }
          simplify.
          apply hyperdoctrine_hyp.
      - do 4 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        pose (y₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h X) ×h X)))))).
        pose (y₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h X) ×h X))))).
        pose (x₁ := π₂ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((((𝟙 ×h Y) ×h Y) ×h X) ×h X))).
        fold x₁ x₂ y₁ y₂.
        use partial_setoid_mor_eq_defined.
        + exact y₁.
        + exact x₁.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          use weaken_right.
          use from_subobject_to_partial_setoid_eq.
          {
            apply monic_to_per_subobject.
          }
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - do 3 use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (y := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Y) ×h X) ×h X))))).
        pose (x₁ := π₂ (π₁ (tm_var (((𝟙 ×h Y) ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var (((𝟙 ×h Y) ×h X) ×h X))).
        fold x₁ x₂ y.
        use to_subobject_to_partial_setoid_eq.
        + use (partial_setoid_mor_unique_im φ).
          * exact y.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + cbn ; unfold ζ.
          simplify.
          use exists_intro.
          {
            exact y.
          }
          simplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - use forall_intro ; cbn.
        use impl_intro.
        use weaken_right.
        use (exists_elim (partial_setoid_mor_hom_exists φ _)).
        + exact (π₂ (tm_var _)).
        + apply hyperdoctrine_hyp.
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h X)))).
          pose (x := π₂ (tm_var ((𝟙 ×h Y) ×h X))).
          fold x y.
          use exists_intro.
          {
            exact x.
          }
          simplify.
          fold y.
          use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.

    Definition monic_to_per_subobject_inv
      : partial_setoid_morphism
          Y
          (subobject_to_partial_setoid monic_to_per_subobject).
    Proof.
      use make_partial_setoid_morphism.
      - exact ξ₂.
      - exact monic_to_per_subobject_inv_laws.
    Defined.

    Proposition monic_to_per_subobject_inv_comm
      : partial_setoid_comp_morphism
          monic_to_per_subobject_inv
          (subobject_to_partial_setoid_incl monic_to_per_subobject)
        =
        partial_setoid_comp_morphism φ (id_partial_setoid_morphism X).
    Proof.
      use eq_partial_setoid_morphism.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right ; cbn ; unfold ξ₂.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (y := π₁ (π₁ (tm_var ((Y ×h X) ×h X)))).
        pose (x₁ := π₂ (π₁ (tm_var ((Y ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((Y ×h X) ×h X))).
        fold x₁ x₂ y.
        use exists_intro.
        {
          exact x₁.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        fold x₁ x₂ y.
        use conj_intro.
        + use partial_setoid_mor_eq_defined.
          * exact y.
          * exact x₂.
          * use weaken_left.
            use (partial_setoid_mor_dom_defined φ y x₂).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right ; cbn ; unfold ξ₂, ζ.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (y := π₁ (π₁ (tm_var ((Y ×h X) ×h X)))).
        pose (x₁ := π₂ (π₁ (tm_var ((Y ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var ((Y ×h X) ×h X))).
        fold x₁ x₂ y.
        use exists_intro.
        {
          exact x₁.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        fold x₁ x₂ y.
        repeat use conj_intro.
        + use partial_setoid_mor_eq_defined.
          * exact y.
          * exact x₂.
          * use weaken_left.
            use (partial_setoid_mor_dom_defined φ y x₂).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
        + use weaken_right.
          exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
        + use exists_intro.
          {
            exact y.
          }
          simplify.
          use partial_setoid_mor_eq_defined.
          * exact y.
          * exact x₂.
          * use weaken_left.
            use (partial_setoid_mor_dom_defined φ y x₂).
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
    Qed.
  End Eso.

  Definition per_subobject_disp_functor_ess_split_surj
    : disp_functor_disp_ess_split_surj per_subobject_disp_functor.
  Proof.
    refine (λ (X : partial_setoid H), _).
    intro f.
    induction f as [ [ Y φ ] p ].
    cbn in Y, φ, p.
    refine (monic_to_per_subobject φ ,, _).
    simple refine (_ ,, _ ,, _ ,, _).
    - simple refine ((_ ,, _) ,, tt) ; cbn.
      + apply monic_to_per_subobject_mor.
        exact p.
      + apply monic_to_per_subobject_mor_eq.
    - simple refine ((_ ,, _) ,, tt) ; cbn.
      + apply monic_to_per_subobject_inv.
      + apply monic_to_per_subobject_inv_comm.
    - apply locally_propositional_mono_cod_disp_cat.
    - apply locally_propositional_mono_cod_disp_cat.
  Defined.
End MonoSubobjectEquiv.
