(******************************************************************************************

 Terminal object in the category of partial setoids

 The category of partial setoids has a terminal object. This terminal object is given by
 the terminal object in the category of types of the hyperdoctrine `H`, and the partial
 equivalence relation is given by the equality formula in `H`.

 Content
 1. Morphism to the terminal object
 2. Uniqueness of the morphism to the terminal object
 3. The terminal object

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Morphism to the terminal object *)
Definition partial_setoid_morphism_to_terminal_form
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : form (X ×h eq_partial_setoid 𝟙)
  := let x := π₁ (tm_var (X ×h 𝟙)) in
     x ~ x.

Arguments partial_setoid_morphism_to_terminal_form {H} X /.

Proposition partial_setoid_morphism_to_terminal_laws
            {H : first_order_hyperdoctrine}
            (X : partial_setoid H)
  : partial_setoid_morphism_laws (partial_setoid_morphism_to_terminal_form X).
Proof.
  unfold partial_setoid_morphism_to_terminal_form.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    cbn ; simplify.
    rewrite partial_setoid_subst.
    simplify.
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h 𝟙)))).
    fold x.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_cod_defined_law.
    cbn ; simplify.
    rewrite partial_setoid_subst.
    simplify.
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h 𝟙)))).
    pose (y := π₂ (tm_var ((𝟙 ×h X) ×h 𝟙))).
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use eq_in_eq_partial_setoid.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_eq_defined_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x₁ x₂ y₁ y₂.
    do 4 use forall_intro.
    use impl_intro.
    use weaken_right.
    do 2 use impl_intro.
    do 2 use weaken_left.
    use partial_setoid_refl_r.
    {
      exact x₁.
    }
    apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x y₁ y₂.
    do 3 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    use hyperdoctrine_unit_tm_eq.
  - unfold partial_setoid_mor_hom_exists_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use exists_intro.
    + exact !!.
    + rewrite partial_setoid_subst.
      simplify.
      apply hyperdoctrine_hyp.
Qed.

Definition partial_setoid_morphism_to_terminal
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : partial_setoid_morphism X (eq_partial_setoid 𝟙).
Proof.
  use make_partial_setoid_morphism.
  - exact (partial_setoid_morphism_to_terminal_form X).
  - exact (partial_setoid_morphism_to_terminal_laws X).
Defined.

(** * 2. Uniqueness of the morphism to the terminal object *)
Proposition parital_setoid_morphism_to_terminal_eq
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            (φ : partial_setoid_morphism X (eq_partial_setoid 𝟙))
  : φ = partial_setoid_morphism_to_terminal X.
Proof.
  pose (x := π₁ (tm_var (X ×h 𝟙))).
  pose (y := π₂ (tm_var (X ×h 𝟙))).
  use eq_partial_setoid_morphism ; cbn ; fold x.
  - use (partial_setoid_mor_dom_defined φ x y).
    unfold x, y.
    rewrite <- hyperdoctrine_pair_eta.
    simplify.
    apply hyperdoctrine_hyp.
  - use (exists_elim (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
    cbn.
    use weaken_right.
    unfold x, y ; clear x y.
    simplify.
    pose (x := π₁ (tm_var ((X ×h 𝟙) ×h 𝟙))).
    pose (y := π₂ (tm_var ((X ×h 𝟙) ×h 𝟙))).
    fold x y.
    assert (y = π₂ x) as p.
    {
      use hyperdoctrine_unit_eq.
    }
    rewrite p.
    rewrite <- (hyperdoctrine_pair_eta x).
    apply hyperdoctrine_hyp.
Qed.

(** * 3. The terminal object *)
Definition terminal_partial_setoid
           (H : first_order_hyperdoctrine)
  : Terminal (category_of_partial_setoids H).
Proof.
  use make_Terminal.
  - exact (eq_partial_setoid 𝟙).
  - intros X.
    use make_iscontr.
    + exact (partial_setoid_morphism_to_terminal X).
    + exact parital_setoid_morphism_to_terminal_eq.
Defined.
