(******************************************************************************************

 The subobject classifier of partial setoids in a tripos

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 Content
 1. The partial setoid representing the subobject classifier
 2. Accessors for the partial equivalence relation
 3. The map representing truth
 4. The universal mapping property of the subobject classifier
 4.1. Maps to the subobject classifier
 4.2. The map gives rise to a pullback square
 4.3. Uniqueness
 5. The subobject classifier of partial setoids

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMonomorphisms.

Local Open Scope cat.
Local Open Scope hd.

Section TriposSubobjectClassifier.
  Context (H : tripos).

  (** * 1. The partial setoid representing the subobject classifier *)
  Definition omega_per_form
    : form ((Ω ×h Ω) : ty H)
    := let Γ := Ω ×h Ω : ty H in
       let φ := Prf [ π₁ (tm_var Γ) ] in
       let ψ := Prf [ π₂ (tm_var Γ) ] in
       φ ⇔ ψ.

  Arguments omega_per_form /.

  Proposition omega_per_axioms
    : per_axioms omega_per_form.
  Proof.
    split.
    - unfold per_symm_axiom ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      pose (φ := Prf [ π₂ (π₁ (tm_var (((𝟙 : ty H) ×h Ω) ×h Ω))) ] ).
      pose (ψ := Prf [ π₂ (tm_var (((𝟙 : ty H) ×h Ω) ×h Ω)) ]).
      fold φ ψ.
      use iff_sym.
      apply hyperdoctrine_hyp.
    - unfold per_trans_axiom ; cbn.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify.
      cbn.
      pose (φ := Prf [ π₂ (π₁ (π₁ (tm_var ((((𝟙 : ty H) ×h Ω) ×h Ω) ×h Ω)))) ]).
      pose (ψ := Prf [ π₂ (π₁ (tm_var ((((𝟙 : ty H) ×h Ω) ×h Ω) ×h Ω))) ]).
      pose (χ := Prf [ π₂ (tm_var ((((𝟙 : ty H) ×h Ω) ×h Ω) ×h Ω)) ]).
      fold φ ψ χ.
      use iff_trans.
      + exact ψ.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition omega_per
    : per (Ω : ty H).
  Proof.
    use make_per.
    - exact omega_per_form.
    - exact omega_per_axioms.
  Defined.

  Definition omega_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact Ω.
    - exact omega_per.
  Defined.

  (** * 2. Accessors for the partial equivalence relation *)
  Proposition eq_in_omega_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {ω₁ ω₂ : tm Γ omega_partial_setoid}
              (p : Δ ⊢ Prf [ ω₁ ] ⇔ Prf [ ω₂ ])
    : Δ ⊢ ω₁ ~ ω₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    simplify.
    exact p.
  Qed.

  Proposition from_eq_in_omega_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {ω₁ ω₂ : tm Γ omega_partial_setoid}
              (p : Δ ⊢ ω₁ ~ ω₂)
    : Δ ⊢ Prf [ ω₁ ] ⇔ Prf [ ω₂ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_omega_partial_setoid_left
              {Γ : ty H}
              {Δ : form Γ}
              {ω₁ ω₂ : tm Γ omega_partial_setoid}
              (p : Δ ⊢ ω₁ ~ ω₂)
              (q : Δ ⊢ Prf [ ω₁ ])
    : Δ ⊢ Prf [ ω₂ ].
  Proof.
    use (iff_elim_left (from_eq_in_omega_partial_setoid p)).
    exact q.
  Qed.

  Proposition from_eq_in_omega_partial_setoid_right
              {Γ : ty H}
              {Δ : form Γ}
              {ω₁ ω₂ : tm Γ omega_partial_setoid}
              (p : Δ ⊢ ω₁ ~ ω₂)
              (q : Δ ⊢ Prf [ ω₂ ])
    : Δ ⊢ Prf [ ω₁ ].
  Proof.
    use (iff_elim_right (from_eq_in_omega_partial_setoid p)).
    exact q.
  Qed.

  (** * 3. The map representing truth  *)
  Definition omega_partial_setoid_true_form
    : form (eq_partial_setoid 𝟙 ×h omega_partial_setoid)
    := Prf [ π₂ (tm_var _) ].

  Arguments omega_partial_setoid_true_form /.

  Proposition omega_partial_setoid_true_laws
    : partial_setoid_morphism_laws omega_partial_setoid_true_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      pose (ω := π₂ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω))).
      pose (t₁ := π₂ (π₁ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω)))).
      pose (t₂ := π₁ (π₁ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω)))).
      fold ω t₁ t₂.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_unit_tm_eq.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      pose (ω := π₂ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω))).
      pose (t₁ := π₂ (π₁ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω)))).
      pose (t₂ := π₁ (π₁ (tm_var (((𝟙 : ty H) ×h 𝟙) ×h Ω)))).
      fold ω t₁ t₂.
      use eq_in_omega_partial_setoid.
      apply iff_refl.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 (use forall_intro).
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      simplify.
      pose (t₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 : ty H) ×h 𝟙) ×h 𝟙) ×h Ω) ×h Ω)))))).
      pose (t₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 : ty H) ×h 𝟙) ×h 𝟙) ×h Ω) ×h Ω))))).
      pose (ω₁ := π₂ (π₁ (tm_var (((((𝟙 : ty H) ×h 𝟙) ×h 𝟙) ×h Ω) ×h Ω)))).
      pose (ω₂ := π₂ (tm_var (((((𝟙 : ty H) ×h 𝟙) ×h 𝟙) ×h Ω) ×h Ω))).
      fold t₁ t₂ ω₁ ω₂.
      use hyp_ltrans.
      use weaken_right.
      use iff_elim_left.
      + exact (Prf [ ω₁ ]).
      + use weaken_left.
        use from_eq_in_omega_partial_setoid.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law ; cbn.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify.
      pose (ω₁ := π₂ (π₁ (tm_var ((((𝟙 : ty H) ×h 𝟙) ×h Ω) ×h Ω)))).
      pose (ω₂ := π₂ (tm_var ((((𝟙 : ty H) ×h 𝟙) ×h Ω) ×h Ω))).
      fold ω₁ ω₂.
      use eq_in_omega_partial_setoid.
      use iff_true_true.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      pose (t₁ := π₁ (tm_var ((𝟙 : ty H) ×h 𝟙))).
      pose (t₂ := π₂ (tm_var ((𝟙 : ty H) ×h 𝟙))).
      use exists_intro.
      {
        exact (tripos_form_to_tm ⊤).
      }
      simplify.
      fold t₁ t₂.
      rewrite tripos_form_to_tm_Prf.
      apply truth_intro.
  Qed.

  Definition omega_partial_setoid_true
    : partial_setoid_morphism (eq_partial_setoid 𝟙) omega_partial_setoid.
  Proof.
    use make_partial_setoid_morphism.
    - exact omega_partial_setoid_true_form.
    - exact omega_partial_setoid_true_laws.
  Defined.

  (** * 4. The universal mapping property of the subobject classifier *)
  Section UMP.
    Context {X Y : partial_setoid H}
            (m : Monic (category_of_partial_setoids H) X Y).

    Let φ : partial_setoid_morphism X Y := pr1 m.

    (** * 4.1. Maps to the subobject classifier *)
    Definition subobject_classifier_partial_setoid_map_form
      : form (Y ×h omega_partial_setoid)
      := let x := π₂ (tm_var ((Y ×h Ω) ×h X)) in
         let y := π₁ (tm_var (Y ×h Ω)) in
         let ω := π₂ (tm_var (Y ×h Ω)) in
         y ~ y
         ∧
         (∃h (φ [ ⟨ x , y [ π₁ (tm_var _) ]tm ⟩ ]) ⇔ Prf [ ω ]).

    Arguments subobject_classifier_partial_setoid_map_form /.

    Proposition subobject_classifier_partial_setoid_map_laws
      : partial_setoid_morphism_laws
          subobject_classifier_partial_setoid_map_form.
    Proof.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        do 2 (use forall_intro).
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h Ω)))).
        pose (ω := π₂ (tm_var ((𝟙 ×h Y) ×h Ω))).
        fold y ω.
        use weaken_left.
        apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        do 2 (use forall_intro).
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h Ω)))).
        pose (ω := π₂ (tm_var ((𝟙 ×h Y) ×h Ω))).
        fold y ω.
        use eq_in_omega_partial_setoid.
        apply iff_refl.
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (y₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω)))))).
        pose (y₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω))))).
        pose (ω₁ := π₂ (π₁ (tm_var ((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω)))).
        pose (ω₂ := π₂ (tm_var ((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω))).
        fold y₁ y₂ ω₁ ω₂.
        use conj_intro.
        + do 2 use weaken_left.
          exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
        + use iff_intro.
          * use (from_eq_in_omega_partial_setoid_left (ω₁ := ω₁) (ω₂ := ω₂)).
            ** do 2 use weaken_left.
               use weaken_right.
               apply hyperdoctrine_hyp.
            ** use (iff_elim_left
                      (weaken_left (weaken_right (weaken_right (hyperdoctrine_hyp _) _) _) _)).
               use hyp_sym.
               use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
               rewrite conj_subst.
               use hyp_ltrans.
               use weaken_right.
               simplify_form.
               unfold y₁, y₂, ω₁, ω₂ ; clear y₁ y₂ ω₁ ω₂.
               rewrite !partial_setoid_subst.
               simplify.
               pose (y₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))))))).
               pose (y₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X)))))).
               pose (ω₁ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))))).
               pose (ω₂ := π₂ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X)))).
               pose (x := π₂ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))).
               cbn.
               fold y₁ y₂ ω₁ ω₂ x.
               use exists_intro.
               {
                 exact x.
               }
               simplify.
               fold y₁.
               use (partial_setoid_mor_eq_defined φ).
               *** exact x.
               *** exact y₂.
               *** use weaken_right.
                   use (partial_setoid_mor_dom_defined φ x y₂).
                   apply hyperdoctrine_hyp.
               *** use partial_setoid_sym.
                   do 3 use weaken_left.
                   apply hyperdoctrine_hyp.
               *** use weaken_right.
                   apply hyperdoctrine_hyp.
          * use weaken_cut.
            ** exact (∃h (φ [⟨ π₂ (tm_var _) , π₂ (π₁ (π₁ (π₁ (π₁ (tm_var _))))) ⟩])).
            ** use iff_elim_right.
               *** exact (Prf [ ω₁ ]).
               *** use weaken_left.
                   do 2 use weaken_right.
                   apply hyperdoctrine_hyp.
               *** use from_eq_in_omega_partial_setoid_left.
                   **** exact ω₂.
                   **** do 2 use weaken_left.
                        use weaken_right.
                        use partial_setoid_sym.
                        apply hyperdoctrine_hyp.
                   **** use weaken_right.
                        apply hyperdoctrine_hyp.
            ** use hyp_sym.
               use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
               rewrite conj_subst.
               use hyp_ltrans.
               use weaken_right.
               simplify_form.
               unfold y₁, y₂, ω₁, ω₂ ; clear y₁ y₂ ω₁ ω₂.
               rewrite !partial_setoid_subst.
               simplify.
               pose (y₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))))))).
               pose (y₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X)))))).
               pose (ω₁ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))))).
               pose (ω₂ := π₂ (π₁ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X)))).
               pose (x := π₂ (tm_var (((((𝟙 ×h Y) ×h Y) ×h Ω) ×h Ω) ×h X))).
               cbn.
               fold y₁ y₂ ω₁ ω₂ x.
               use exists_intro.
               {
                 exact x.
               }
               simplify.
               fold y₂.
               use (partial_setoid_mor_eq_defined
                      φ
                      _ _
                      (weaken_right (hyperdoctrine_hyp _) _)).
               *** use weaken_right.
                   use (partial_setoid_mor_dom_defined φ x y₁).
                   apply hyperdoctrine_hyp.
               *** do 4 use weaken_left.
                   apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law ; cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (y := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Y) ×h Ω) ×h Ω))))).
        pose (ω₁ := π₂ (π₁ (tm_var (((𝟙 ×h Y) ×h Ω) ×h Ω)))).
        pose (ω₂ := π₂ (tm_var (((𝟙 ×h Y) ×h Ω) ×h Ω))).
        fold y ω₁ ω₂.
        use impl_intro.
        use eq_in_omega_partial_setoid.
        use iff_intro.
        + use (iff_elim_left
                 (weaken_left (weaken_right (weaken_right (hyperdoctrine_hyp _) _) _) _)).
          use (iff_elim_right
                 (weaken_left (weaken_left (weaken_right (hyperdoctrine_hyp _) _) _) _)).
          use weaken_right.
          apply hyperdoctrine_hyp.
        + use (iff_elim_left
                 (weaken_left (weaken_left (weaken_right (hyperdoctrine_hyp _) _) _) _)).
          use (iff_elim_right
                 (weaken_left (weaken_right (weaken_right (hyperdoctrine_hyp _) _) _) _)).
          use weaken_right.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law ; cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        pose (y := π₂ (tm_var (𝟙 ×h Y))).
        fold y.
        use exists_intro.
        {
          exact (tripos_form_to_tm (∃h (φ [ ⟨ π₂ (tm_var _) , π₂ (π₁ (tm_var _)) ⟩ ]))).
        }
        simplify_form.
        rewrite partial_setoid_subst.
        unfold y.
        simplify.
        rewrite tripos_form_to_tm_Prf.
        use conj_intro.
        + apply hyperdoctrine_hyp.
        + apply iff_refl.
    Qed.

    Definition subobject_classifier_partial_setoid_map
      : partial_setoid_morphism Y omega_partial_setoid.
    Proof.
      use make_partial_setoid_morphism.
      - exact subobject_classifier_partial_setoid_map_form.
      - exact subobject_classifier_partial_setoid_map_laws.
    Defined.

    Proposition subobject_classifier_partial_setoid_comm
      : partial_setoid_comp_morphism
          φ
          subobject_classifier_partial_setoid_map
        =
        partial_setoid_comp_morphism
          (partial_setoid_morphism_to_terminal X)
          omega_partial_setoid_true.
    Proof.
      use eq_partial_setoid_morphism ; cbn.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite exists_subst.
        use exists_intro.
        {
          exact !!.
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Ω) ×h Y)))).
        pose (ω := π₂ (π₁ (tm_var ((X ×h Ω) ×h Y)))).
        pose (y := π₂ (tm_var ((X ×h Ω) ×h Y))).
        fold x ω y.
        use conj_intro.
        + use (partial_setoid_mor_dom_defined φ).
          * exact y.
          * use weaken_left.
            apply hyperdoctrine_hyp.
        + use (iff_elim_left (weaken_right (weaken_right (hyperdoctrine_hyp _) _) _)).
          use exists_intro.
          * exact x.
          * simplify.
            use weaken_left.
            apply hyperdoctrine_hyp.
      - use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        use (exists_elim (partial_setoid_mor_hom_exists φ (weaken_left (hyperdoctrine_hyp _) _))).
        rewrite exists_subst.
        use exists_intro.
        {
          exact (π₂ (tm_var _)).
        }
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (π₁ (tm_var (((X ×h Ω) ×h 𝟙) ×h Y))))).
        pose (ω := π₂ (π₁ (π₁ (tm_var (((X ×h Ω) ×h 𝟙) ×h Y))))).
        pose (y := π₂ (tm_var (((X ×h Ω) ×h 𝟙) ×h Y))).
        fold x ω y.
        repeat use conj_intro.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + use (partial_setoid_mor_cod_defined φ).
          * exact x.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + use impl_intro.
          do 2 use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + use impl_intro.
          use exists_intro.
          * exact x.
          * simplify.
            use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    (** * 4.2. The map gives rise to a pullback square *)
    Section PullbackUMP.
      Context {W : partial_setoid H}
              (ψ₁ : partial_setoid_morphism W Y)
              (ψ₂ : partial_setoid_morphism W (eq_partial_setoid 𝟙))
              (q : partial_setoid_comp_morphism
                     ψ₁
                     subobject_classifier_partial_setoid_map
                   =
                   partial_setoid_comp_morphism
                     ψ₂
                     omega_partial_setoid_true).

      Definition is_pullback_subobject_classifier_partial_setoid_map_form
        : form (W ×h X)
        := let w := π₁ (π₁ (tm_var ((W ×h X) ×h Y))) in
           let x := π₂ (π₁ (tm_var ((W ×h X) ×h Y))) in
           let y := π₂ (tm_var ((W ×h X) ×h Y)) in
           (∃h (φ [ ⟨ x , y ⟩ ] ∧ ψ₁ [ ⟨ w , y ⟩ ])).

      Arguments is_pullback_subobject_classifier_partial_setoid_map_form /.

      Proposition is_pullback_subobject_classifier_partial_setoid_map_laws
        : partial_setoid_morphism_laws
            is_pullback_subobject_classifier_partial_setoid_map_form.
      Proof.
        repeat split.
        - unfold partial_setoid_mor_dom_defined_law ; cbn.
          do 2 use forall_intro.
          use impl_intro.
          use weaken_right.
          rewrite exists_subst.
          use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (w := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h Y))))).
          pose (x := π₂ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((𝟙 ×h W) ×h X) ×h Y))).
          fold w x y.
          use weaken_right.
          use (partial_setoid_mor_dom_defined ψ₁ w y).
          apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_cod_defined_law ; cbn.
          do 2 use forall_intro.
          use impl_intro.
          use weaken_right.
          rewrite exists_subst.
          use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (w := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h Y))))).
          pose (x := π₂ (π₁ (tm_var (((𝟙 ×h W) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((𝟙 ×h W) ×h X) ×h Y))).
          fold w x y.
          use weaken_left.
          use (partial_setoid_mor_dom_defined φ x y).
          apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_eq_defined_law ; cbn.
          do 4 use forall_intro.
          use impl_intro.
          use weaken_right.
          do 2 use impl_intro.
          use hyp_sym.
          rewrite exists_subst.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (w₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h W) ×h X) ×h X) ×h Y))))))).
          pose (w₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h W) ×h X) ×h X) ×h Y)))))).
          pose (x₁ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h W) ×h X) ×h X) ×h Y))))).
          pose (x₂ := π₂ (π₁ (tm_var (((((𝟙 ×h W) ×h W) ×h X) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((((𝟙 ×h W) ×h W) ×h X) ×h X) ×h Y))).
          fold w₁ w₂ x₁ x₂ y.
          use exists_intro.
          {
            exact y.
          }
          simplify.
          fold x₂ w₂.
          use conj_intro.
          + use (partial_setoid_mor_eq_defined φ).
            * exact x₁.
            * exact y.
            * use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
            * do 2 use weaken_right.
              use (partial_setoid_mor_cod_defined ψ₁ w₁).
              apply hyperdoctrine_hyp.
            * use weaken_right.
              use weaken_left.
              apply hyperdoctrine_hyp.
          + use (partial_setoid_mor_eq_defined ψ₁).
            * exact w₁.
            * exact y.
            * do 2 use weaken_left.
              apply hyperdoctrine_hyp.
            * do 2 use weaken_right.
              use (partial_setoid_mor_cod_defined ψ₁ w₁).
              apply hyperdoctrine_hyp.
            * do 2 use weaken_right.
              apply hyperdoctrine_hyp.
        - unfold partial_setoid_mor_unique_im_law ; cbn.
          rewrite !exists_subst.
          do 3 use forall_intro.
          use impl_intro.
          use weaken_right.
          use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          simplify_form.
          use impl_intro.
          use hyp_sym.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (w := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h X) ×h X) ×h Y) ×h Y))))))).
          pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h X) ×h X) ×h Y) ×h Y)))))).
          pose (x₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h W) ×h X) ×h X) ×h Y) ×h Y))))).
          pose (y₁ := π₂ (π₁ (tm_var (((((𝟙 ×h W) ×h X) ×h X) ×h Y) ×h Y)))).
          pose (y₂ := π₂ (tm_var (((((𝟙 ×h W) ×h X) ×h X) ×h Y) ×h Y))).
          fold w x₁ x₂ y₁ y₂.
          pose (Δ := (φ [⟨ x₁, y₁ ⟩] ∧ ψ₁ [⟨ w, y₁ ⟩]) ∧ φ [⟨ x₂, y₂ ⟩] ∧ ψ₁ [⟨ w, y₂ ⟩]).
          pose (Δ' := φ [⟨ x₁, y₁ ⟩] ∧ φ [⟨ x₂, y₁ ⟩]).
          assert (r : Δ ⊢ Δ').
          {
            unfold Δ, Δ'.
            use conj_intro.
            + do 2 use weaken_left.
              apply hyperdoctrine_hyp.
            + use (partial_setoid_mor_eq_defined φ).
              * exact x₂.
              * exact y₂.
              * use weaken_right.
                use weaken_left.
                use (partial_setoid_mor_dom_defined φ x₂ y₂).
                apply hyperdoctrine_hyp.
              * use (partial_setoid_mor_unique_im ψ₁).
                ** exact w.
                ** do 2 use weaken_right.
                   apply hyperdoctrine_hyp.
                ** use weaken_left.
                   use weaken_right.
                   apply hyperdoctrine_hyp.
              * use weaken_right.
                use weaken_left.
                apply hyperdoctrine_hyp.
          }
          refine (hyperdoctrine_cut r _).
          unfold Δ'.
          (*
           Key lemma:
             if `φ` is monic
             then `φ [⟨ x₁, y₁ ⟩] ∧ φ [⟨ x₂, y₁ ⟩] ⊢ x₁ ~ x₂`
           *)
          (* we need that `φ` is monic *)
          (* the part in MonicLemma needs to be generalized *)
          admit.
        - unfold partial_setoid_mor_hom_exists_law ; cbn.
          use forall_intro.
          use impl_intro.
          use weaken_right.
          pose (w := π₂ (tm_var (𝟙 ×h W))).
          fold w.
          pose (from_eq_partial_setoid_morphism_b
                  q
                  (t₁ := w) (t₂ := tripos_form_to_tm ⊤)
                  (Δ := w ~ w)).
          cbn -[tripos_form_to_tm] in h.
          rewrite !exists_subst in h.
          use (exists_elim (h _)).
          + simplify.
            use exists_intro.
            {
              exact !!.
            }
            simplify.
            rewrite tripos_form_to_tm_Prf.
            use conj_intro ; [ | apply truth_intro ].
            use (exists_elim (partial_setoid_mor_hom_exists ψ₂ (hyperdoctrine_hyp _))).
            use weaken_right.
            unfold w.
            simplify.
            use (hyperdoctrine_eq_transportf _ _ (hyperdoctrine_hyp _)).
            use hyperdoctrine_eq_pair_right.
            apply hyperdoctrine_unit_tm_eq.
          + unfold w.
            simplify_form.
            rewrite !partial_setoid_subst.
            simplify.
            rewrite <- hyperdoctrine_comp_subst.
            rewrite tripos_form_to_tm_Prf.
            simplify_form.
            refine (weaken_cut _ _).
            {
              do 3 use weaken_right.
              use (iff_elim_right (hyperdoctrine_hyp _)).
              apply truth_intro.
            }
            refine (exists_elim _ _).
            {
              use weaken_right.
              apply hyperdoctrine_hyp.
            }
            rewrite !conj_subst.
            use hyp_sym.
            use hyp_rtrans.
            use weaken_left.
            do 3 use hyp_rtrans.
            use weaken_left.
            simplify_form.
            rewrite !partial_setoid_subst.
            simplify.
            use exists_intro.
            {
              exact (π₂ (tm_var _)).
            }
            rewrite exists_subst.
            use exists_intro.
            {
              exact (π₂ (π₁ (tm_var _))).
            }
            simplify.
            clear w h.
            pose (x := π₂ (tm_var (((𝟙 ×h W) ×h Y) ×h X))).
            pose (y := π₂ (π₁ (tm_var (((𝟙 ×h W) ×h Y) ×h X)))).
            pose (w := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h W) ×h Y) ×h X))))).
            fold x y w.
            use conj_intro.
            * do 3 use weaken_left.
              apply hyperdoctrine_hyp.
            * use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
      Admitted.

      Definition is_pullback_subobject_classifier_partial_setoid_map
        : partial_setoid_morphism W X.
      Proof.
        use make_partial_setoid_morphism.
        - exact is_pullback_subobject_classifier_partial_setoid_map_form.
        - exact is_pullback_subobject_classifier_partial_setoid_map_laws.
      Defined.

      Proposition is_pullback_subobject_classifier_partial_setoid_map_pr1
        : partial_setoid_comp_morphism
            is_pullback_subobject_classifier_partial_setoid_map
            φ
          =
          ψ₁.
      Proof.
        use eq_partial_setoid_morphism ; cbn.
        - use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          rewrite exists_subst.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          simplify.
          pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y))))).
          pose (y₁ := π₂ (π₁ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y))))).
          pose (x := π₂ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y)))).
          pose (y₂ := π₂ (tm_var (((W ×h Y) ×h X) ×h Y))).
          fold w x y₁ y₂.
          rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var _)))).
          fold w y₁.
          use (partial_setoid_mor_eq_defined ψ₁).
          + exact w.
          + exact y₂.
          + use (partial_setoid_mor_dom_defined ψ₁).
            * exact y₂.
            * do 2 use weaken_right.
              apply hyperdoctrine_hyp.
          + use (partial_setoid_mor_unique_im φ).
            * exact x.
            * use weaken_right.
              use weaken_left.
              apply hyperdoctrine_hyp.
            * use weaken_left.
              apply hyperdoctrine_hyp.
          + do 2 use weaken_right.
            apply hyperdoctrine_hyp.
        - use (exists_elim
                 (partial_setoid_mor_hom_exists
                    is_pullback_subobject_classifier_partial_setoid_map
                    _)).
          + exact (π₁ (tm_var _)).
          + use (partial_setoid_mor_dom_defined ψ₁).
            * exact (π₂ (tm_var _)).
            * rewrite <- hyperdoctrine_pair_eta.
              simplify.
              apply hyperdoctrine_hyp.
          + cbn.
            rewrite exists_subst.
            use hyp_sym.
            use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
            rewrite conj_subst.
            use hyp_ltrans.
            use weaken_right.
            simplify.
            pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y))))).
            pose (y₁ := π₂ (π₁ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y))))).
            pose (x := π₂ (π₁ (tm_var (((W ×h Y) ×h X) ×h Y)))).
            pose (y₂ := π₂ (tm_var (((W ×h Y) ×h X) ×h Y))).
            fold w x y₁ y₂.
            use exists_intro.
            {
              exact x.
            }
            simplify_form.
            assert (ψ₁ [⟨ w, y₁ ⟩] ∧ φ [⟨ x, y₂ ⟩] ∧ ψ₁ [⟨ w, y₂ ⟩] ⊢ φ [⟨ x, y₁ ⟩]) as r.
            {
              use (partial_setoid_mor_eq_defined φ).
              * exact x.
              * exact y₂.
              * use weaken_right.
                use weaken_left.
                use (partial_setoid_mor_dom_defined φ x y₂).
                apply hyperdoctrine_hyp.
              * use partial_setoid_sym.
                use (partial_setoid_mor_unique_im ψ₁).
                ** exact w.
                ** use weaken_left.
                   apply hyperdoctrine_hyp.
                ** do 2 use weaken_right.
                   apply hyperdoctrine_hyp.
              * use weaken_right.
                use weaken_left.
                apply hyperdoctrine_hyp.
            }
            use conj_intro.
            * use exists_intro.
              {
                exact y₁.
              }
              simplify.
              fold w.
              rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var _)))).
              fold w y₁.
              use conj_intro.
              ** exact r.
              ** use weaken_left.
                 apply hyperdoctrine_hyp.
            * simplify.
              fold y₁.
              rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var _)))).
              fold w y₁.
              exact r.
      Qed.

      Proposition is_pullback_subobject_classifier_partial_setoid_map_pr2
        : partial_setoid_comp_morphism
            is_pullback_subobject_classifier_partial_setoid_map
            (partial_setoid_morphism_to_terminal X)
          =
          ψ₂.
      Proof.
        apply (TerminalArrowEq (T := terminal_partial_setoid H)).
      Qed.

      Context {ζ : partial_setoid_morphism W X}
              (ζp : partial_setoid_comp_morphism ζ φ = ψ₁)
              (ζq : partial_setoid_comp_morphism
                      ζ
                      (partial_setoid_morphism_to_terminal X)
                    =
                    ψ₂).

      Proposition is_pullback_subobject_classifier_partial_setoid_unique
        : ζ = is_pullback_subobject_classifier_partial_setoid_map.
      Proof.
        use eq_partial_setoid_morphism ; cbn.
        - use (exists_elim (partial_setoid_mor_hom_exists φ _)).
          + exact (π₂ (tm_var _)).
          + use (partial_setoid_mor_cod_defined ζ).
            {
              exact (π₁ (tm_var _)).
            }
            rewrite <- hyperdoctrine_pair_eta.
            simplify.
            apply hyperdoctrine_hyp.
          + rewrite exists_subst.
            pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h Y)))).
            pose (x := π₂ (π₁ (tm_var ((W ×h X) ×h Y)))).
            pose (y := π₂ (tm_var ((W ×h X) ×h Y))).
            use exists_intro.
            {
              exact y.
            }
            simplify.
            fold w x y.
            rewrite (hyperdoctrine_pair_eta (π₁ (tm_var _))).
            fold w x.
            use conj_intro.
            * use weaken_right.
              apply hyperdoctrine_hyp.
            * use (from_eq_partial_setoid_morphism_f ζp) ; cbn.
              simplify_form.
              use exists_intro.
              {
                exact x.
              }
              simplify.
              apply hyperdoctrine_hyp.
        - use (exists_elim (hyperdoctrine_hyp _)).
          use weaken_right.
          pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h Y)))).
          pose (x := π₂ (π₁ (tm_var ((W ×h X) ×h Y)))).
          pose (y := π₂ (tm_var ((W ×h X) ×h Y))).
          fold w x y.
          rewrite (hyperdoctrine_pair_eta (π₁ (tm_var _))).
          fold w x.
          refine (weaken_cut
                    (from_eq_partial_setoid_morphism_b
                       ζp
                       (weaken_right (hyperdoctrine_hyp _) _))
                    _).
          cbn.
          simplify_form.
          use hyp_sym.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          unfold w, x, y.
          clear w x y.
          simplify.
          pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h X) ×h Y) ×h X))))).
          pose (x₁ := π₂ (π₁ (π₁ (tm_var (((W ×h X) ×h Y) ×h X))))).
          pose (y := π₂ (π₁ (tm_var (((W ×h X) ×h Y) ×h X)))).
          pose (x₂ := π₂ (tm_var (((W ×h X) ×h Y) ×h X))).
          fold w x₁ x₂ y.
          use (partial_setoid_mor_eq_defined ζ).
          + exact w.
          + exact x₂.
          + use weaken_left.
            use weaken_right.
            use (partial_setoid_mor_dom_defined ψ₁ w y).
            apply hyperdoctrine_hyp.
          + (* use that φ is monic *)
            use partial_setoid_sym.
            admit.
          + use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
      Admitted.
    End PullbackUMP.

    Definition is_pullback_subobject_classifier_partial_setoid
      : isPullback
          (C := category_of_partial_setoids H)
          subobject_classifier_partial_setoid_comm.
    Proof.
      intros W ψ₁ ψ₂ q.
      use make_iscontr.
      - simple refine (_ ,, _ ,, _).
        + exact (is_pullback_subobject_classifier_partial_setoid_map ψ₁ ψ₂ q).
        + exact (is_pullback_subobject_classifier_partial_setoid_map_pr1 ψ₁ ψ₂ q).
        + exact (is_pullback_subobject_classifier_partial_setoid_map_pr2 ψ₁ ψ₂ q).
      - abstract
          (intros ζ ;
           use subtypePath ;
           [ intro ;
             apply isapropdirprod ;
             apply homset_property
           | ] ;
           induction ζ as [ ζ [ ζp ζq ]] ;
           exact (is_pullback_subobject_classifier_partial_setoid_unique _ _ _ ζp ζq)).
    Defined.

    (** * 4.3. Uniqueness *)
    Context (χ : partial_setoid_morphism Y omega_partial_setoid)
            (p : partial_setoid_comp_morphism φ χ
                 =
                 partial_setoid_comp_morphism
                   (partial_setoid_morphism_to_terminal X)
                   omega_partial_setoid_true)
            (Hχ : isPullback
                    (C := category_of_partial_setoids H)
                    p).

    Proposition subobject_classifier_partial_setoid_map_unique
      : χ = subobject_classifier_partial_setoid_map.
    Proof.
      use eq_partial_setoid_morphism ; cbn.
      - pose (y := π₁ (tm_var (Y ×h Ω))).
        pose (ω := π₂ (tm_var (Y ×h Ω))).
        fold y ω.
        use conj_intro.
        + use (partial_setoid_mor_dom_defined χ y ω).
          unfold y, ω.
          rewrite <- hyperdoctrine_pair_eta.
          simplify.
          apply hyperdoctrine_hyp.
        + use iff_intro.
          * use hyp_sym.
            use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
            rewrite conj_subst.
            use hyp_ltrans.
            use weaken_right.
            simplify_form.
            unfold y, ω ; clear y ω.
            simplify.
            pose (y := π₁ (π₁ (tm_var ((Y ×h Ω) ×h X)))).
            pose (ω := π₂ (π₁ (tm_var ((Y ×h Ω) ×h X)))).
            pose (x := π₂ (tm_var ((Y ×h Ω) ×h X))).
            fold y ω x.
            rewrite (hyperdoctrine_pair_eta (π₁ (tm_var _))).
            fold y ω.
            pose (from_eq_partial_setoid_morphism_f
                    p
                    (t₁ := x) (t₂ := ω)
                    (Δ := χ [⟨ y, ω ⟩] ∧ φ [⟨ x, y ⟩]))
              as r.
            cbn in r.
            rewrite !exists_subst in r.
            use (exists_elim (r _)) ; clear r.
            ** use exists_intro.
               {
                 exact y.
               }
               simplify.
               use hyp_sym.
               apply hyperdoctrine_hyp.
            ** unfold y, ω, x ; clear x y ω.
               simplify_form.
               rewrite partial_setoid_subst.
               simplify.
               pose (y := π₁ (π₁ (π₁ (tm_var (((Y ×h Ω) ×h X) ×h 𝟙))))).
               pose (ω := π₂ (π₁ (π₁ (tm_var (((Y ×h Ω) ×h X) ×h 𝟙))))).
               pose (x := π₂ (π₁ (tm_var (((Y ×h Ω) ×h X) ×h 𝟙)))).
               fold x y ω.
               do 2 use weaken_right.
               apply hyperdoctrine_hyp.
          * (* pullback assumption needed *)
            admit.
      - use (exists_elim
               (partial_setoid_mor_hom_exists
                  χ
                  (weaken_left (hyperdoctrine_hyp _) _))).
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (y := π₁ (π₁ (tm_var ((Y ×h Ω) ×h Ω)))).
        pose (ω₁ := π₂ (π₁ (tm_var ((Y ×h Ω) ×h Ω)))).
        pose (ω₂ := π₂ (tm_var ((Y ×h Ω) ×h Ω))).
        cbn.
        fold y ω₁ ω₂.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((Y ×h Ω) ×h Ω)))).
        fold y ω₁.
        use (partial_setoid_mor_eq_defined χ).
        + exact y.
        + exact ω₂.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use partial_setoid_sym.
          use eq_in_omega_partial_setoid.
          use iff_intro.
          * pose (((y ~ y
                    ∧ (∃h (φ [⟨ π₂ (tm_var _) , π₁ (π₁ (π₁ (tm_var _))) ⟩]) ⇔ Prf [ ω₁ ]))
                    ∧ χ [⟨ y, ω₂ ⟩]) ∧ Prf [ ω₁ ])
              as Δ.
            pose (y ~ y
                  ∧ χ [⟨ y, ω₂ ⟩]
                  ∧ (∃h (φ [⟨ π₂ (tm_var _) , π₁ (π₁ (π₁ (tm_var _))) ⟩])))
              as Δ'.
            assert (Δ ⊢ Δ') as r.
            {
              unfold Δ, Δ'.
              repeat use conj_intro.
              ** do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
              ** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
              ** use iff_elim_right.
                 *** exact (Prf [ ω₁ ]).
                 *** do 2 use weaken_left.
                     use weaken_right.
                     apply hyperdoctrine_hyp.
                 *** use weaken_right.
                     apply hyperdoctrine_hyp.
            }
            refine (hyperdoctrine_cut r _).
            unfold Δ'.
            use hyp_rtrans.
            use hyp_sym.
            use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
            rewrite conj_subst.
            use hyp_ltrans.
            use weaken_right.
            unfold y, ω₁, ω₂, Δ, Δ' ; clear r Δ Δ' y ω₁ ω₂.
            simplify_form.
            rewrite partial_setoid_subst.
            simplify.
            pose (y := π₁ (π₁ (π₁ (tm_var (((Y ×h Ω) ×h Ω) ×h X))))).
            pose (ω₁ := π₂ (π₁ (π₁ (tm_var (((Y ×h Ω) ×h Ω) ×h X))))).
            pose (ω₂ := π₂ (π₁ (tm_var (((Y ×h Ω) ×h Ω) ×h X)))).
            pose (x := π₂ (tm_var (((Y ×h Ω) ×h Ω) ×h X))).
            cbn.
            fold y ω₁ ω₂ x.
            pose (from_eq_partial_setoid_morphism_f
                    p
                    (t₁ := x) (t₂ := ω₂)
                    (Δ := (y ~ y ∧ χ [⟨ y, ω₂ ⟩]) ∧ φ [⟨ x, y ⟩]))
              as r.
            cbn in r.
            rewrite !exists_subst in r.
            use (exists_elim (r _)).
            ** use exists_intro.
               {
                 exact y.
               }
               simplify.
               use hyp_ltrans.
               use weaken_right.
               use hyp_sym.
               apply hyperdoctrine_hyp.
            ** simplify_form.
               rewrite !partial_setoid_subst.
               simplify.
               do 2 use weaken_right.
               apply hyperdoctrine_hyp.
          * (* from pullback *)
            admit.
        + use weaken_right.
          apply hyperdoctrine_hyp.
    Admitted.
  End UMP.

  (** * 5. The subobject classifier of partial setoids *)
  Definition subobject_classifier_partial_setoid
    : subobject_classifier (terminal_partial_setoid H).
  Proof.
    use make_subobject_classifier_cat.
    - exact omega_partial_setoid.
    - exact omega_partial_setoid_true.
    - intros X Y m.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (subobject_classifier_partial_setoid_map m).
        * exact (subobject_classifier_partial_setoid_comm m).
        * exact (is_pullback_subobject_classifier_partial_setoid m).
      + abstract
          (intros χ ;
           use subtypePath ;
           [ intro ;
             use isaproptotal2 ;
             [ intro ; apply isaprop_isPullback
             | intros ; apply homset_property ]
           | ] ;
           induction χ as [ χ [ p Hχ ] ] ;
           cbn ;
           exact (subobject_classifier_partial_setoid_map_unique m χ p Hχ)).
  Defined.
End TriposSubobjectClassifier.

Arguments omega_per_form H /.
Arguments omega_partial_setoid_true_form H /.
Arguments subobject_classifier_partial_setoid_map_form {H X Y} m /.
Arguments is_pullback_subobject_classifier_partial_setoid_map_form {H X Y} m {W} ψ₁ ψ₂ q /.
