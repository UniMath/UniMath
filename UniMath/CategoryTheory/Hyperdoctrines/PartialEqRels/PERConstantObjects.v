(******************************************************************************************

 The constant object functor

 Every type gives rise to a partial setoid whose partial equivalence relation is given by
 the equality formula in the hyperdoctrine. In "Tripos Theory in Retrospect" by Andrew Pitts,
 these are called 'constant objects'. In this file, we show that this construction gives
 rise to a functor from the category of types to the category of partial setoids. Here
 the key step lies inn showing that every term gives rise to a partial setoid morphism.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Every term gives a partial setoid morphism
 2. The constant object functor

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Every term gives a partial setoid morphism *)
Definition term_partial_setoid_morphism_form
           {H : first_order_hyperdoctrine}
           {X Y : ty H}
           (t : tm X Y)
  : form (eq_partial_setoid X ×h eq_partial_setoid Y)
  := t [ π₁ (tm_var _) ]tm ≡ π₂ (tm_var _).

Arguments term_partial_setoid_morphism_form {H X Y} t /.

Proposition term_partial_setoid_morphism_laws
            {H : first_order_hyperdoctrine}
            {X Y : ty H}
            (t : tm X Y)
  : partial_setoid_morphism_laws (term_partial_setoid_morphism_form t).
Proof.
  unfold term_partial_setoid_morphism_form.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_cod_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_eq_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x₁ x₂ y₁ y₂.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use impl_intro.
    use impl_intro.
    simplify.
    use hyperdoctrine_eq_trans.
    + exact y₁.
    + use hyperdoctrine_eq_trans.
      * exact (t [ x₁ ]tm).
      * use hyperdoctrine_subst_eq.
        use hyperdoctrine_eq_sym.
        do 2 use weaken_left.
        use weaken_right.
        use from_eq_in_eq_partial_setoid.
        apply hyperdoctrine_hyp.
      * use weaken_right.
        apply hyperdoctrine_hyp.
    + use weaken_left.
      use weaken_right.
      use from_eq_in_eq_partial_setoid.
      apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x y₁ y₂.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    use hyperdoctrine_eq_trans.
    + exact (t [ x ]tm).
    + use weaken_left.
      use weaken_right.
      use hyperdoctrine_eq_sym.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_hom_exists_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use impl_intro.
    unfold x, y.
    simplify.
    use exists_intro.
    + exact (t [ π₂ (tm_var _) ]tm).
    + simplify.
      apply hyperdoctrine_refl.
Qed.

Definition term_partial_setoid_morphism
           {H : first_order_hyperdoctrine}
           {X Y : ty H}
           (t : tm X Y)
  : partial_setoid_morphism (eq_partial_setoid X) (eq_partial_setoid Y).
Proof.
  use make_partial_setoid_morphism.
  - exact (term_partial_setoid_morphism_form t).
  - exact (term_partial_setoid_morphism_laws t).
Defined.

(** * 2. The constant object functor *)
Section ConstantObject.
  Context (H : first_order_hyperdoctrine).

  Definition functor_to_partial_setoids_data
    : functor_data
        (hyperdoctrine_type_category H)
        (category_of_partial_setoids H).
  Proof.
    use make_functor_data.
    - exact (λ X, eq_partial_setoid X).
    - exact (λ _ _ t, term_partial_setoid_morphism t).
  Defined.

  Proposition functor_to_partial_setoids_laws
    : is_functor functor_to_partial_setoids_data.
  Proof.
    split.
    - refine (λ (X : ty H), _).
      use eq_partial_setoid_morphism ; cbn in *.
      + use eq_in_eq_partial_setoid.
        use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
        use hyperdoctrine_refl_eq.
        refine (!_).
        exact (var_tm_subst (π₁ (tm_var (X ×h X)))).
      + use (hyperdoctrine_cut (from_eq_in_eq_partial_setoid (hyperdoctrine_hyp _))).
        use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
        use hyperdoctrine_refl_eq.
        exact (var_tm_subst (π₁ (tm_var (X ×h X)))).
    - refine (λ (X Y Z : ty H) (t₁ : tm X Y) (t₂ : tm Y Z), _).
      use eq_partial_setoid_morphism ; cbn in *.
      + use exists_intro.
        * exact (t₁ [ π₁ (tm_var _) ]tm).
        * simplify.
          use conj_intro.
          ** apply hyperdoctrine_refl.
          ** use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
             use hyperdoctrine_refl_eq.
             exact (!(tm_subst_comp (π₁ (tm_var (X ×h Z))) t₁ t₂)).
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use (hyperdoctrine_eq_trans _ (weaken_right (hyperdoctrine_hyp _) _)).
        use weaken_left.
        use hyperdoctrine_eq_trans.
        * exact (t₂ [ t₁ [π₁ (π₁ (tm_var ((X ×h Z) ×h Y))) ]tm ]tm).
        * use hyperdoctrine_refl_eq.
          exact (tm_subst_comp _ t₁ t₂).
        * use hyperdoctrine_subst_eq.
          apply hyperdoctrine_hyp.
  Qed.

  Definition functor_to_partial_setoids
    : hyperdoctrine_type_category H ⟶ category_of_partial_setoids H.
  Proof.
    use make_functor.
    - exact functor_to_partial_setoids_data.
    - exact functor_to_partial_setoids_laws.
  Defined.
End ConstantObject.
