(******************************************************************************************

 Monomorphisms into constant partial setoids

 In this file, we study monomorphisms into constant partial setoids. Let us be more precise
 on what this entails. Suppose that we have a first-order hyperdoctrine `H`, and let `C`
 be the category of types of `H`. We write `Form` for the displayed category over `C` whose
 objects over `Γ` are formulas in context `Γ`. The hyperdoctrine `H` gives rise to a category
 of partial setoids, which we denote by `PartialSetoid`. We already showed that we have a
 functor, call it `F`, from the category `C` of types to `PartialSetoid`. It sends every type
 to the partial setoid whose partial equivalence relation is given by the equality formula
 in the hyperdoctrine `H`. In this file, we construct a displayed functor over `F` from `Form`
 to the displayed category of monomorphisms in `PartialSetoid`. Concretely, this means that
 every formula in `H` gives rise to a monomorphism into a constant object in the category of
 partial setoids. We also show that this displayed functor is both split essentially surjective
 and fully faithful. Intuitively, this means that monomorphisms into a constant object are the
 same as formulas on it.

 This statement is similar to Lemma 3.3 in "Tripos Theory in Retrospect" by Andrew Pitts.
 The difference is that we are looking at constant objects, i.e., partial setoids whose
 partial equivalence relation is given by equality. For this reason, the extra requirements
 given in Formulas (7) and (8) become vacuous, and as a result, subobjects of `X` are the
 same as formulas on `X`.

 There is an important consequence of this construction. Since the displayed functor from
 formulas in `H` to monomorphisms in the category of partial setoids is split essentially
 surjective and fully faithful, it gives rise to an equivalence of fiber categories. As such,
 it preserves all structure, and it is a morphism of first-order hyperdoctrines. This allows
 us to reason about constant objects in the category of partial objects by using the language
 of the first-order hyperdoctrine.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Formulas to monomorphisms
 1.1. The partial setoid
 1.2. Accessors for the partial equivalence relation
 1.3. The inclusion
 1.4. The proof that it is monic
 2. Proofs to commuting triangles
 2.1. The morphism from a proof
 2.2. Proof of commutativity
 3. The displayed functor from formulas to monomorphisms
 4. The displayed functor is fully faithful
 5. The displayed functor is split essentially surjective

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
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERConstantObjects.

Local Open Scope cat.
Local Open Scope hd.

Section FormulaFunctor.
  Context (H : first_order_hyperdoctrine).

  (** * 1. Formulas to monomorphisms *)

  (** * 1.1. The partial setoid *)
  Definition formula_to_per_form
             {A : ty H}
             (φ : form A)
    : form (A ×h A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Arguments formula_to_per_form /.

  Proposition formula_to_per_axioms
              {A : ty H}
              (φ : form A)
    : per_axioms (formula_to_per_form φ).
  Proof.
    split ; cbn.
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

  (** * 1.2. Accessors for the partial equivalence relation *)
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
    simplify.
    use hyperdoctrine_eq_transportf.
    - exact t₁.
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 1.3. The inclusion *)
  Definition formula_to_partial_setoid_incl_form
             {A : ty H}
             (φ : form A)
    : form (formula_to_partial_setoid φ ×h eq_partial_setoid A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Arguments formula_to_partial_setoid_incl_form {A} φ /.

  Proposition formula_to_partial_setoid_incl_laws
              {A : ty H}
              (φ : form A)
    : partial_setoid_morphism_laws (formula_to_partial_setoid_incl_form φ).
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
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
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_refl.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
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
    - unfold partial_setoid_mor_unique_im_law ; cbn.
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
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
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

  (** * 1.4. The proof that it is monic *)
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

  (** * 2. Proofs to commuting triangles *)

  (** * 2.1. The morphism from a proof *)
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

  Arguments proof_to_partial_setoid_morphism_form {Γ₁ Γ₂ Δ φ s} q /.

  Proposition proof_to_partial_setoid_morphism_laws
              {Γ₁ Γ₂ : ty H}
              {Δ : form Γ₁}
              {φ : form Γ₂}
              {s : tm Γ₁ Γ₂}
              (q : Δ ⊢ φ [ s ])
    : partial_setoid_morphism_laws (proof_to_partial_setoid_morphism_form q).
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_formula_to_partial_setoid.
      + apply hyperdoctrine_refl.
      + use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_formula_to_partial_setoid.
      + apply hyperdoctrine_refl.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
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
        * exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
        * exact (prop_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
      + use conj_intro.
        * use weaken_left.
          use weaken_right.
          use hyperdoctrine_eq_transportf.
          ** apply y₁.
          ** exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
          ** exact (prop_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
        * use hyperdoctrine_eq_trans.
          ** exact y₁.
          ** use hyperdoctrine_eq_sym.
             use weaken_left.
             use weaken_right.
             exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
          ** use hyperdoctrine_eq_trans.
             *** exact (s [ x₁ ]tm).
             *** do 3 use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use hyperdoctrine_subst_eq.
                 do 2 use weaken_left.
                 exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_unique_im_law ; cbn.
      simplify.
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
      pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
      pose (y₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))).
      fold x y₁ y₂.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use eq_in_formula_to_partial_setoid.
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
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
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
        * exact (prop_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
        * use conj_intro.
          ** refine (hyperdoctrine_cut
                       (prop_from_formula_to_partial_setoid
                          _
                          (hyperdoctrine_hyp _))
                       _).
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

  (** * 2.2. Proof of commutativity *)
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
    - use (exists_elim (hyperdoctrine_hyp _)) ; cbn.
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
    - use (exists_elim (hyperdoctrine_hyp _)) ; cbn.
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

  (** * 3. The displayed functor from formulas to monomorphisms *)
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

  (** * 4. The displayed functor is fully faithful *)
  Definition partial_setoids_disp_functor_ff
    : disp_functor_ff partial_setoids_disp_functor.
  Proof.
    refine (λ (X Y : ty H) (φ : form X) (ψ : form Y) (s : tm X Y), _).
    use isweqimplimpl.
    - intro p.
      use to_disp_mor_hyperdoctrine.
      cbn in p.
      induction p as [ p t ].
      induction t.
      induction p as [ χ p ].
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

  (** * 5. The displayed functor is split essentially surjective *)
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

    Arguments partial_setoids_disp_functor_eso_form /.

    Definition partial_setoids_disp_functor_eso_mor_form
      : form (formula_to_partial_setoid partial_setoids_disp_functor_eso_form ×h X)
      := let a := π₁ (tm_var (A ×h X)) in
         let x := π₂ (tm_var (A ×h X)) in
         φ [ ⟨ x , a ⟩ ].

    Arguments partial_setoids_disp_functor_eso_mor_form /.

    (**
       The following definitions and lemmas are used to apply the assumption that
       `φ` is monic. To use this assumption, we need to give a suitable partial
       setoid and maps from it to `X`. These are defined in this section.
     *)
    Section MonicLemma.
      Context {Γ : ty H}
              (Δ : form Γ)
              (t : tm Γ X)
              (p : Δ ⊢ t ~ t).

      Let ζ : form (formula_to_partial_setoid Δ ×h X)
        := Δ [ π₁ (tm_var _) ] ∧ π₂ (tm_var _) ~ t [ π₁ (tm_var _) ]tm.

      Local Lemma point_partial_setoid_morphism_laws
        : partial_setoid_morphism_laws ζ.
      Proof.
        unfold ζ.
        repeat split.
        - unfold partial_setoid_mor_dom_defined_law ; cbn.
          repeat (use forall_intro).
          use impl_intro.
          use weaken_right.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use eq_in_formula_to_partial_setoid.
          + apply hyperdoctrine_refl.
          + use weaken_left.
            apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_cod_defined_law ; cbn.
          repeat (use forall_intro).
          use impl_intro.
          use weaken_right.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use weaken_right.
          exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
        - unfold partial_setoid_mor_eq_defined_law ; cbn.
          repeat (use forall_intro).
          use impl_intro.
          use weaken_right.
          do 2 use impl_intro.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (γ₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ) ×h Γ) ×h X) ×h X)))))).
          pose (γ₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ) ×h Γ) ×h X) ×h X))))).
          pose (x₁ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ) ×h Γ) ×h X) ×h X)))).
          pose (x₂ := π₂ (tm_var ((((𝟙 ×h Γ) ×h Γ) ×h X) ×h X))).
          fold γ₁ γ₂ x₁ x₂.
          pose (Δ' := (γ₁ ≡ γ₂ ∧ x₁ ~ x₂) ∧ Δ [ γ₁ ] ∧ x₁ ~ t [γ₁ ]tm).
          use (hyperdoctrine_cut (ψ := Δ')).
          {
            unfold Δ', partial_setoid_formula ; cbn.
            simplify.
            repeat (use conj_intro).
            + do 3 use weaken_left.
              apply hyperdoctrine_hyp.
            + use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
            + do 2 use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
            + do 2 use weaken_right.
              apply hyperdoctrine_hyp.
          }
          unfold Δ'.
          use conj_intro.
          + use hyperdoctrine_eq_transportf.
            * exact γ₁.
            * do 2 use weaken_left.
              apply hyperdoctrine_hyp.
            * use weaken_right.
              use weaken_left.
              apply hyperdoctrine_hyp.
          + use partial_setoid_trans.
            * exact x₁.
            * use weaken_left.
              use weaken_right.
              use partial_setoid_sym.
              apply hyperdoctrine_hyp.
            * use partial_setoid_trans.
              ** exact (t [ γ₁ ]tm).
              ** do 2 use weaken_right.
                 apply hyperdoctrine_hyp.
              ** use partial_setoid_path_to_eq.
                 *** do 2 use weaken_right.
                     exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
                 *** do 2 use weaken_left.
                     use hyperdoctrine_subst_eq.
                     apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_unique_im_law ; cbn.
          repeat (use forall_intro).
          use impl_intro.
          use weaken_right.
          use impl_intro.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          use partial_setoid_trans.
          + exact (t [ π₂ (π₁ (π₁ (tm_var _))) ]tm).
          + use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          + do 2 use weaken_right.
            use partial_setoid_sym.
            apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_hom_exists_law ; cbn.
          repeat (use forall_intro).
          use impl_intro.
          use weaken_right.
          use exists_intro.
          + exact (t [ π₂ (tm_var _) ]tm).
          + simplify_form.
            rewrite !partial_setoid_subst.
            simplify.
            simplify.
            use conj_intro.
            * exact (prop_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
            * refine (hyperdoctrine_cut
                        (prop_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _))
                        _).
              refine (hyperdoctrine_cut
                        (hyperdoctrine_proof_subst _ p)
                        _).
              rewrite partial_setoid_subst.
              apply hyperdoctrine_hyp.
      Qed.

      Definition point_partial_setoid_morphism
        : partial_setoid_morphism (formula_to_partial_setoid Δ) X.
      Proof.
        use make_partial_setoid_morphism.
        - exact ζ.
        - exact point_partial_setoid_morphism_laws.
      Defined.
    End MonicLemma.

    Proposition partial_setoids_disp_functor_eso_mor_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_mor_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_mor_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use eq_in_formula_to_partial_setoid.
        + apply hyperdoctrine_refl.
        + simplify_form.
          use exists_intro.
          * exact (π₂ (tm_var _)).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        refine (partial_setoid_mor_eq_defined φ _ _ (weaken_right (hyperdoctrine_hyp _) _)).
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_left ; cbn.
          use eq_in_eq_partial_setoid.
          exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_unique_im_law ; cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (x₁ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X)))).
        pose (x₂ := π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X))).
        pose (a := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X))))).
        pose (Δ := φ [⟨ x₁ , a ⟩] ∧ φ [⟨ x₂ , a ⟩]).
        fold x₁ x₂ a.
        assert (Δ ⊢ x₁ ~ x₁) as r₁.
        {
          unfold Δ.
          use (partial_setoid_mor_dom_defined φ _ a).
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ x₂ ~ x₂) as r₂.
        {
          unfold Δ.
          use (partial_setoid_mor_dom_defined φ _ a).
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        enough (partial_setoid_comp_morphism (point_partial_setoid_morphism Δ x₁ r₁) φ
                =
                partial_setoid_comp_morphism (point_partial_setoid_morphism Δ x₂ r₂) φ)
          as r₃.
        {
          pose (Hφ _ _ _ r₃) as p.
          refine (hyperdoctrine_cut
                    (@from_eq_partial_setoid_morphism_f _ _ _ _ _ p _ Δ (tm_var _) x₁ _)
                    _).
          + cbn.
            unfold Δ.
            simplify_form.
            rewrite partial_setoid_subst.
            simplify.
            use conj_intro.
            * apply hyperdoctrine_hyp.
            * use weaken_left.
              use (partial_setoid_mor_dom_defined φ x₁ a).
              apply hyperdoctrine_hyp.
          + cbn.
            unfold Δ.
            simplify_form.
            rewrite partial_setoid_subst.
            simplify.
            use weaken_right.
            apply hyperdoctrine_hyp.
        }
        use eq_partial_setoid_morphism ; cbn.
        + use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          simplify_form.
          use exists_intro.
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * rewrite !partial_setoid_subst.
            simplify.
            unfold x₁, x₂.
            rewrite !partial_setoid_subst.
            simplify.
            repeat (use conj_intro).
            ** do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** unfold Δ, x₁, x₂.
               rewrite !conj_subst.
               do 2 use weaken_left.
               use weaken_right.
               simplify.
               exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
            ** unfold Δ, x₁, a, x₂ ; clear Δ x₁ a x₂ r₁ r₂.
               simplify.
               pose (a₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))))))).
               pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X)))))).
               pose (x₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))))).
               pose (a₂ := π₂ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X)))).
               pose (x₃ := π₂ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))).
               cbn.
               fold a₁ a₂ x₁ x₂ x₃.
               use (partial_setoid_mor_eq_defined φ).
               *** exact x₂.
               *** exact a₁.
               *** do 2 use weaken_left.
                   use weaken_right.
                   exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
               *** use (partial_setoid_mor_unique_im φ).
                   **** exact x₁.
                   **** do 3 use weaken_left.
                        apply hyperdoctrine_hyp.
                   **** do 2 use hyp_ltrans.
                        do 2 use weaken_right.
                        pose (Δ := x₃ ~ x₁ ∧ φ [⟨ x₃ , a₂ ⟩]).
                        assert (Δ ⊢ x₃ ~ x₁) as q₁.
                        {
                          use weaken_left.
                          apply hyperdoctrine_hyp.
                        }
                        assert (Δ ⊢ (a₂ : tm _ (eq_partial_setoid _)) ~ a₂) as q₂.
                        {
                          use weaken_right.
                          exact (partial_setoid_mor_cod_defined
                                   φ
                                   _ _
                                   (hyperdoctrine_hyp _)).
                        }
                        use (partial_setoid_mor_eq_defined φ q₁ q₂).
                        use weaken_right.
                        apply hyperdoctrine_hyp.
               *** do 2 use weaken_left.
                   use weaken_right.
                   apply hyperdoctrine_hyp.
        + use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          simplify_form.
          use exists_intro.
          * exact (π₂ (π₁ (π₁ (π₁ (tm_var _))))).
          * rewrite !partial_setoid_subst.
            simplify.
            rewrite !partial_setoid_subst.
            simplify.
            unfold x₁, x₂.
            simplify.
            repeat (use conj_intro).
            ** do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** unfold Δ, x₁, x₂.
               do 2 use weaken_left.
               rewrite conj_subst.
               use weaken_left.
               simplify.
               exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
            ** unfold Δ, x₁, a, x₂.
               simplify.
               clear Δ x₁ a x₂ r₁ r₂.
               pose (a₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))))))).
               pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X)))))).
               pose (x₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))))).
               pose (a₂ := π₂ (π₁ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X)))).
               pose (x₃ := π₂ (tm_var (((((𝟙 ×h A) ×h X) ×h X) ×h A) ×h X))).
               cbn.
               fold a₁ a₂ x₁ x₂ x₃.
               use (partial_setoid_mor_eq_defined φ).
               *** exact x₁.
               *** exact a₁.
               *** do 3 use weaken_left.
                   exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
               *** use (partial_setoid_mor_unique_im φ).
                   **** exact x₂.
                   **** do 2 use weaken_left.
                        use weaken_right.
                        apply hyperdoctrine_hyp.
                   **** do 2 use hyp_ltrans.
                        do 2 use weaken_right.
                        pose (Δ := x₃ ~ x₂ ∧ φ [⟨ x₃ , a₂ ⟩]).
                        assert (Δ ⊢ x₃ ~ x₂) as q₁.
                        {
                          use weaken_left.
                          apply hyperdoctrine_hyp.
                        }
                        assert (Δ ⊢ (a₂ : tm _ (eq_partial_setoid _)) ~ a₂) as q₂.
                        {
                          use weaken_right.
                          exact (partial_setoid_mor_cod_defined
                                   φ
                                   _ _
                                   (hyperdoctrine_hyp _)).
                        }
                        use (partial_setoid_mor_eq_defined φ q₁ q₂).
                        use weaken_right.
                        apply hyperdoctrine_hyp.
               *** do 3 use weaken_left.
                   apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law ; cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula.
        cbn.
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

    Arguments partial_setoids_disp_functor_eso_inv_form /.

    Proposition partial_setoids_disp_functor_eso_inv_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_inv_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_inv_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use eq_in_formula_to_partial_setoid.
        + use from_eq_in_eq_partial_setoid.
          exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
        + simplify_form.
          use exists_intro.
          * exact (π₂ (π₁ (tm_var _))).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
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
          unfold partial_setoid_formula ; cbn.
          rewrite conj_subst.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law ; cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        use eq_in_formula_to_partial_setoid.
        + use from_eq_in_eq_partial_setoid.
          use (partial_setoid_mor_unique_im φ).
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + simplify_form.
          use exists_intro.
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * simplify.
            use weaken_left.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law ; cbn.
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
    simple refine (_ ,, _).
    - exact (partial_setoids_disp_functor_eso_form (pr21 f)).
    - simple refine (_ ,, _ ,, _ ,, _).
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_mor.
          exact (pr2 f).
        * apply partial_setoids_disp_functor_eso_mor_comm.
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_inv.
        * apply partial_setoids_disp_functor_eso_inv_comm.
      + apply locally_propositional_mono_cod_disp_cat.
      + apply locally_propositional_mono_cod_disp_cat.
  Defined.
End FormulaFunctor.

Arguments formula_to_per_form {H A} φ /.
Arguments formula_to_partial_setoid_incl_form {H A} φ /.
Arguments proof_to_partial_setoid_morphism_form {H Γ₁ Γ₂ Δ φ s} q /.
Arguments partial_setoids_disp_functor_eso_form {H A X} φ /.
Arguments partial_setoids_disp_functor_eso_mor_form {H A X} φ /.
Arguments partial_setoids_disp_functor_eso_inv_form {H A X} φ /.
