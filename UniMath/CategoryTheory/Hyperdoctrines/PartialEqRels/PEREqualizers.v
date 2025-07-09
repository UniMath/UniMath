(******************************************************************************************

 Equalizers of partial setoids

 In this file, we show that the category of partial setoids has equalizers. Since in other
 files we showed that this category has binary products and a terminal object, this allows
 us to conclude that the category of partial setoids has finite limits, which is a key
 ingredient in the tripos-to-topos construction.

 Suppose that we have partial setoids `X` and `Y` and partial setoid morphisms `φ` and `ψ`
 from `X` to `Y`. To construct the equalizer of `φ` and `ψ`, we need to find a suitable
 subtype of `X`. We do so by defining an alternative partial equivalence relation on the
 type `X` (see [equalizer_per]). Intuitively, we identify two elements `x` and `y` if
 they are identified according to the partial equivalence relation of `X` and if there is
 a `y` such that `φ` and `ψ` map `x` to `y`. This is essentially what is written in the
 formula under [equalizer_per_form].

 Content
 1. The equalizer partial setoid
 2. Accessors for the partial equivalence relation of the equalizer
 3. The inclusion of the equalizer
 4. The universal property of the equalizer
 4.1. The map from the universal property
 4.2. Uniqueness of the morphism
 5. Equalizers of partial setoids

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.

Local Open Scope cat.
Local Open Scope hd.

Section PartialEquivalenceRelationEqualizer.
  Context {H : first_order_hyperdoctrine}
          {X Y : partial_setoid H}
          (φ ψ : partial_setoid_morphism X Y).

  (** * 1. The equalizer partial setoid *)
  Definition equalizer_per_form
    : form (X ×h X)
    := let x := π₁ (tm_var (X ×h X)) in
       let x' := π₂ (tm_var (X ×h X)) in
       let y := π₂ (tm_var ((X ×h X) ×h Y)) in
       x ~ x'
       ∧
       (∃h (φ [ ⟨ x [ π₁ (tm_var _) ]tm , y ⟩ ]
            ∧
            ψ [ ⟨ x [ π₁ (tm_var _) ]tm , y ⟩ ])).

  Arguments equalizer_per_form /.

  Proposition equalizer_per_axioms
    : per_axioms equalizer_per_form.
  Proof.
    repeat split ; cbn.
    - pose (x := π₁ (tm_var (X ×h X))).
      pose (x' := π₂ (tm_var (X ×h X))).
      pose (y := π₂ (tm_var ((X ×h X) ×h Y))).
      fold x x' y.
      unfold per_symm_axiom.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      unfold x, x', y ; clear x x' y.
      hypersimplify.
      use conj_intro.
      + pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X)))).
        pose (x' := π₂ (tm_var ((𝟙 ×h X) ×h X))).
        fold x x'.
        use weaken_left.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      + use (exists_elim (weaken_right (hyperdoctrine_hyp _) _)).
        use hyp_sym.
        simplify_form.
        rewrite partial_setoid_subst.
        use hyp_rtrans.
        use weaken_left.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * hypersimplify.
          pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y))))).
          pose (x' := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h Y))).
          fold x x' y.
          use conj_intro.
          ** use (partial_setoid_mor_eq_defined φ).
             *** exact x.
             *** exact y.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** do 2 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_eq_defined ψ).
             *** exact x.
             *** exact y.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      simplify_form.
      hypersimplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h X))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use impl_intro.
      use hyp_rtrans.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use conj_intro.
      + unfold x₁, x₂, x₃ ; clear x₁ x₂ x₃.
        hypersimplify.
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))))).
        pose (x₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₃ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))).
        fold x₁ x₂ x₃ y₁ y₂.
        use partial_setoid_trans.
        * exact x₂.
        * do 3 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + use exists_intro.
        * exact (π₂ (tm_var _)).
        * unfold x₁, x₂, x₃ ; clear x₁ x₂ x₃.
          simplify_form.
          hypersimplify.
          pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))))).
          pose (x₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))))).
          pose (x₃ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))).
          pose (y₁ := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))).
          pose (y₂ := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))).
          fold x₁ x₂ x₃ y₁ y₂.
          use conj_intro.
          ** use (partial_setoid_mor_eq_defined φ).
             *** exact x₂.
             *** exact y₂.
             *** use partial_setoid_sym.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 use (partial_setoid_mor_cod_defined ψ x₂).
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_eq_defined ψ).
             *** exact x₂.
             *** exact y₂.
             *** use partial_setoid_sym.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 use (partial_setoid_mor_cod_defined ψ x₂).
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 apply hyperdoctrine_hyp.
  Qed.

  Definition equalizer_per
    : per X.
  Proof.
    use make_per.
    - exact equalizer_per_form.
    - exact equalizer_per_axioms.
  Defined.

  Definition equalizer_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact X.
    - exact equalizer_per.
  Defined.

  (** * 2. Accessors for the partial equivalence relation of the equalizer *)

  (**
     The following definition gives more convenient notation for terms in the equalizer
     of two morphisms.
   *)
  Definition equalizer_partial_setoid_to_type
             {Γ : ty H}
             (t : tm Γ equalizer_partial_setoid)
    : tm Γ X
    := t.

  Notation "'ι'" := equalizer_partial_setoid_to_type.

  Proposition eq_in_equalizer_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ ι t₁ ~ ι t₂)
              (q : Δ ⊢ ∃h (φ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]
                           ∧
                           ψ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]))
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    refine (weaken_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    simplify_form.
    hypersimplify.
    use conj_intro.
    - use weaken_right.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      exact q.
  Qed.

  Proposition from_eq_in_equalizer_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ι t₁ ~ ι t₂.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    rewrite conj_subst.
    use weaken_left.
    hypersimplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_equalizer_partial_setoid_ex
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ∃h (φ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]
              ∧
              ψ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]).
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    rewrite conj_subst.
    use weaken_right.
    hypersimplify.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The inclusion of the equalizer *)
  Definition equalizer_partial_setoid_morphism_form
    : form (equalizer_partial_setoid ×h X)
    := let x₁ := π₁ (tm_var _) in
       let x₂ := π₂ (tm_var _) in
       x₁ ~ x₂.

  Arguments equalizer_partial_setoid_morphism_form /.

  Proposition equalizer_partial_setoid_morphism_laws
    : partial_setoid_morphism_laws equalizer_partial_setoid_morphism_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      hypersimplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      hypersimplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use partial_setoid_refl_r.
      + exact x.
      + use from_eq_in_equalizer_partial_setoid.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x₁ x₂ y₁ y₂.
      cbn.
      hypersimplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use partial_setoid_trans.
      + exact x₁.
      + use partial_setoid_sym.
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use partial_setoid_trans.
        * exact y₁.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use hyp_ltrans.
          use weaken_right.
          use eq_in_equalizer_partial_setoid.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use from_eq_in_equalizer_partial_setoid_ex.
             *** exact x₁.
             *** use partial_setoid_sym.
                 apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y₁ y₂.
      cbn.
      hypersimplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use hyperdoctrine_cut.
      + exact (ι x ~ ι y₁ ∧ ι x ~ ι y₂).
      + use conj_intro.
        * use weaken_left.
          use from_eq_in_equalizer_partial_setoid.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use from_eq_in_equalizer_partial_setoid.
          apply hyperdoctrine_hyp.
      + use partial_setoid_trans.
        * exact (ι x).
        * use partial_setoid_sym.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      hypersimplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      unfold x, y ; clear x y.
      simplify_form.
      hypersimplify.
      cbn.
      pose (x := π₂ (tm_var (𝟙 ×h X))).
      fold x.
      apply hyperdoctrine_hyp.
  Qed.

  Definition equalizer_partial_setoid_morphism
    : partial_setoid_morphism equalizer_partial_setoid X.
  Proof.
    use make_partial_setoid_morphism.
    - exact equalizer_partial_setoid_morphism_form.
    - exact equalizer_partial_setoid_morphism_laws.
  Defined.

  Proposition equalizer_partial_setoid_morphism_eq
    : partial_setoid_comp_morphism equalizer_partial_setoid_morphism φ
      =
      partial_setoid_comp_morphism equalizer_partial_setoid_morphism ψ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify_form.
      hypersimplify.
      use (exists_elim
             (from_eq_in_equalizer_partial_setoid_ex
                _ _
                (weaken_left (hyperdoctrine_hyp _) _))).
      simplify_form.
      hypersimplify.
      use exists_intro.
      + exact (π₂ (π₁ (tm_var _))).
      + simplify_form.
        hypersimplify.
        cbn.
        pose (x₁ := π₁ (π₁ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y))))).
        pose (y₁ := π₂ (π₁ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y))))).
        pose (x₂ := π₂ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((X ×h Y) ×h X) ×h Y))).
        fold x₁ y₁ x₂ y₂.
        use conj_intro.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_eq_defined ψ).
          ** exact x₁.
          ** exact y₂.
          ** do 2 use weaken_left.
             use (from_eq_in_equalizer_partial_setoid x₁ x₂).
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_unique_im φ).
             *** exact x₁.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 use (partial_setoid_mor_eq_defined φ).
                 **** exact x₂.
                 **** exact y₁.
                 **** use partial_setoid_sym.
                      use weaken_left.
                      use (from_eq_in_equalizer_partial_setoid x₁ x₂).
                      apply hyperdoctrine_hyp.
                 **** use weaken_right.
                      exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
                 **** use weaken_right.
                      apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify_form.
      hypersimplify.
      use (exists_elim
             (from_eq_in_equalizer_partial_setoid_ex
                _ _
                (weaken_left (hyperdoctrine_hyp _) _))).
      simplify_form.
      hypersimplify.
      use exists_intro.
      + exact (π₂ (π₁ (tm_var _))).
      + simplify_form.
        hypersimplify.
        cbn.
        pose (x₁ := π₁ (π₁ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y))))).
        pose (y₁ := π₂ (π₁ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y))))).
        pose (x₂ := π₂ (π₁ (tm_var (((X ×h Y) ×h X) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((X ×h Y) ×h X) ×h Y))).
        fold x₁ y₁ x₂ y₂.
        use conj_intro.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_eq_defined φ).
          ** exact x₁.
          ** exact y₂.
          ** do 2 use weaken_left.
             use (from_eq_in_equalizer_partial_setoid x₁ x₂).
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_unique_im ψ).
             *** exact x₂.
             *** use (partial_setoid_mor_eq_defined ψ).
                 **** exact x₁.
                 **** exact y₂.
                 **** do 2 use weaken_left.
                      use (from_eq_in_equalizer_partial_setoid x₁ x₂).
                      apply hyperdoctrine_hyp.
                 **** do 2 use weaken_right.
                      exact (partial_setoid_mor_cod_defined ψ _ _ (hyperdoctrine_hyp _)).
                 **** do 2 use weaken_right.
                      apply hyperdoctrine_hyp.
             *** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The universal property of the equalizer *)
  Context {W : partial_setoid H}
          (χ : partial_setoid_morphism W X)
          (p : partial_setoid_comp_morphism χ φ
               =
               partial_setoid_comp_morphism χ ψ).

  (** * 4.1. The map from the universal property *)
  Definition morphism_to_equalizer_partial_setoid_form
    : form (W ×h equalizer_partial_setoid)
    := let w := π₁ (tm_var (W ×h X)) in
       let x := π₂ (tm_var (W ×h X)) in
       χ [ ⟨ w , x ⟩ ].

  Arguments morphism_to_equalizer_partial_setoid_form /.

  Proposition morphism_to_equalizer_partial_setoid_laws_eq
              {Γ : ty H}
              (w : tm Γ W)
              (x : tm Γ X)
    : let s := π₁ (tm_var (Γ ×h Y)) in
      let y := π₂ (tm_var (Γ ×h Y)) in
      χ [ ⟨ w , x ⟩ ]
      ⊢
      (∃h (φ [ ⟨ x [ s ]tm , y ⟩ ] ∧ ψ [ ⟨ x [ s ]tm , y ⟩ ])).
  Proof.
    cbn.
    assert (χ [⟨ w, x ⟩] ⊢ x ~ x) as r.
    {
      use (partial_setoid_mor_cod_defined χ w x).
      apply hyperdoctrine_hyp.
    }
    use (exists_elim (partial_setoid_mor_hom_exists φ r)).
    hypersimplify.
    pose (s := π₁ (tm_var (Γ ×h Y))).
    pose (y := π₂ (tm_var (Γ ×h Y))).
    pose (Δ := χ [⟨ w [s ]tm, x [s ]tm ⟩] ∧ φ [⟨ x [s ]tm, y ⟩]).
    fold s y Δ.
    use (weaken_cut
           (from_eq_partial_setoid_morphism_f p (t₁ := w [ s ]tm) (t₂ := y) _)).
    - cbn.
      simplify_form.
      use exists_intro.
      * exact (x [ s ]tm).
      * unfold y, Δ.
        hypersimplify.
        apply hyperdoctrine_hyp.
    - cbn.
      simplify_form.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      rewrite exists_subst.
      use exists_intro.
      + exact (π₂ (π₁ (tm_var _))).
      + unfold Δ, s, y.
        clear Δ s y.
        hypersimplify.
        use conj_intro.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * pose (s := π₁ (π₁ (tm_var ((Γ ×h Y) ×h X)))).
          pose (y := π₂ (π₁ (tm_var ((Γ ×h Y) ×h X)))).
          pose (x' := π₂ (tm_var ((Γ ×h Y) ×h X))).
          fold s y x'.
          use (partial_setoid_mor_eq_defined ψ).
          ** exact x'.
          ** exact y.
          ** use (partial_setoid_mor_unique_im χ).
             *** exact (w [ s ]tm).
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_cod_defined φ (x [ s ]tm)).
             use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  Proposition morphism_to_equalizer_partial_setoid_laws
    : partial_setoid_morphism_laws morphism_to_equalizer_partial_setoid_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X)))).
      pose (x := π₂ (tm_var ((𝟙 ×h W) ×h X))).
      fold w x.
      use (partial_setoid_mor_dom_defined χ w x).
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X)))).
      pose (x := π₂ (tm_var ((𝟙 ×h W) ×h X))).
      fold w x.
      use eq_in_equalizer_partial_setoid.
      + use (partial_setoid_mor_cod_defined χ w x).
        apply hyperdoctrine_hyp.
      + apply morphism_to_equalizer_partial_setoid_laws_eq.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      hypersimplify.
      pose (w₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h W) ×h W) ×h X) ×h X)))))).
      pose (w₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h W) ×h W) ×h X) ×h X))))).
      pose (x₁ := π₂ (π₁ (tm_var ((((𝟙 ×h W) ×h W) ×h X) ×h X)))).
      pose (x₂ := π₂ (tm_var ((((𝟙 ×h W) ×h W) ×h X) ×h X))).
      fold w₁ w₂ x₁ x₂.
      use (partial_setoid_mor_eq_defined χ).
      + exact w₁.
      + exact x₁.
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use (from_eq_in_equalizer_partial_setoid x₁ x₂).
        use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law ; cbn.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      hypersimplify.
      pose (w := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h X))))).
      pose (x₁ := π₂ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h X)))).
      pose (x₂ := π₂ (tm_var (((𝟙 ×h W) ×h X) ×h X))).
      fold w x₁ x₂.
      use eq_in_equalizer_partial_setoid.
      + use (partial_setoid_mor_unique_im χ).
        * exact w.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        apply morphism_to_equalizer_partial_setoid_laws_eq.
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (partial_setoid_mor_hom_exists χ (hyperdoctrine_hyp _))).
      simplify_form.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify_form.
        hypersimplify.
        pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X)))).
        pose (x := π₂ (tm_var ((𝟙 ×h W) ×h X))).
        fold w x.
        use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition morphism_to_equalizer_partial_setoid
    : partial_setoid_morphism W equalizer_partial_setoid.
  Proof.
    use make_partial_setoid_morphism.
    - exact morphism_to_equalizer_partial_setoid_form.
    - exact morphism_to_equalizer_partial_setoid_laws.
  Defined.

  Proposition morphism_to_equalizer_partial_setoid_eq
    : partial_setoid_comp_morphism
        morphism_to_equalizer_partial_setoid
        equalizer_partial_setoid_morphism
      =
      χ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify_form.
      hypersimplify.
      pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X)))).
      pose (x₁ := π₂ (π₁ (tm_var ((W ×h X) ×h X)))).
      pose (x₂ := π₂ (tm_var ((W ×h X) ×h X))).
      fold w x₁ x₂.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h X) ×h X)))).
      fold w x₁.
      use (partial_setoid_mor_eq_defined χ).
      + exact w.
      + exact x₂.
      + use weaken_left.
        exact (partial_setoid_mor_dom_defined χ _ _ (hyperdoctrine_hyp _)).
      + use weaken_right.
        use (from_eq_in_equalizer_partial_setoid x₂ x₁).
        apply hyperdoctrine_hyp.
      + use weaken_left.
        apply hyperdoctrine_hyp.
    - use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify_form.
        hypersimplify.
        rewrite <- hyperdoctrine_pair_eta.
        hypersimplify.
        pose (w := π₁ (tm_var (W ×h X))).
        pose (x := π₂ (tm_var (W ×h X))).
        fold w x.
        use conj_intro.
        * apply hyperdoctrine_hyp.
        * use eq_in_equalizer_partial_setoid.
          ** use (partial_setoid_mor_cod_defined χ w x).
             unfold w, x.
             rewrite <- hyperdoctrine_pair_eta.
             hypersimplify.
             apply hyperdoctrine_hyp.
          ** rewrite <- (hyperdoctrine_id_subst χ).
             rewrite (hyperdoctrine_pair_eta (tm_var (W ×h X))).
             apply morphism_to_equalizer_partial_setoid_laws_eq.
  Qed.

  Context {ζ : partial_setoid_morphism W equalizer_partial_setoid}
          (q : partial_setoid_comp_morphism ζ equalizer_partial_setoid_morphism
               =
               χ).

  (** * 4.2. Uniqueness of the morphism *)
  Proposition morphism_to_equalizer_partial_setoid_unique
    : ζ = morphism_to_equalizer_partial_setoid.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (from_eq_partial_setoid_morphism_f q) ; cbn.
      simplify_form.
      rewrite partial_setoid_subst.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify_form.
        hypersimplify.
        rewrite <- hyperdoctrine_pair_eta.
        simplify_form.
        pose (w := π₁ (tm_var (W ×h X))).
        pose (x := π₂ (tm_var (W ×h X))).
        cbn.
        fold w x.
        use conj_intro.
        * apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_cod_defined ζ w x).
          unfold w, x.
          rewrite <- hyperdoctrine_pair_eta.
          simplify_form.
          apply hyperdoctrine_hyp.
    - pose (w := π₁ (tm_var (W ×h X))).
      pose (x := π₂ (tm_var (W ×h X))).
      fold w x.
      pose (from_eq_partial_setoid_morphism_b q (hyperdoctrine_hyp (χ [ ⟨ w , x ⟩ ]))) as r.
      cbn in r.
      rewrite exists_subst in r.
      use (exists_elim r).
      unfold w, x ; clear r w x.
      simplify_form.
      hypersimplify.
      (* simplify. *)
      pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X)))).
      pose (x₁ := π₂ (π₁ (tm_var ((W ×h X) ×h X)))).
      pose (x₂ := π₂ (tm_var ((W ×h X) ×h X))).
      fold w x₁ x₂.
      change (π₂ (π₁ (tm_var ((W ×h X) ×h X)))) with x₁.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h X) ×h X)))).
      fold w x₁.
      use weaken_right.
      use (partial_setoid_mor_eq_defined ζ).
      + exact w.
      + exact x₂.
      + use weaken_left.
        use (partial_setoid_mor_dom_defined ζ w x₂).
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        apply hyperdoctrine_hyp.
  Qed.
End PartialEquivalenceRelationEqualizer.

Arguments equalizer_per_form {H X Y} φ ψ /.
Arguments equalizer_partial_setoid_morphism_form {H X Y} φ ψ /.
Arguments morphism_to_equalizer_partial_setoid_form {H X Y φ ψ W} χ.

(** * 5. Equalizers of partial setoids *)
Definition equalizers_partial_setoid
           (H : first_order_hyperdoctrine)
  : Equalizers (category_of_partial_setoids H).
Proof.
  intros X Y φ ψ.
  use make_Equalizer.
  - exact (equalizer_partial_setoid φ ψ).
  - exact (equalizer_partial_setoid_morphism φ ψ).
  - exact (equalizer_partial_setoid_morphism_eq φ ψ).
  - intros W χ p.
    use make_iscontr.
    + simple refine (_ ,, _) ; cbn.
      * exact (morphism_to_equalizer_partial_setoid φ ψ χ p).
      * exact (morphism_to_equalizer_partial_setoid_eq φ ψ χ p).
    + abstract
        (intros ζ ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
           apply morphism_to_equalizer_partial_setoid_unique ;
         exact (pr2 ζ)).
Defined.
