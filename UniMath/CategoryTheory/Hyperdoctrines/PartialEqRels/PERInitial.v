(******************************************************************************************

 The initial partial setoid

 The category of partial setoids has a strict initial object. The idea behind its
 construction is as follows: we define a partial equivalence relation on the unit type and
 we identify none of the objects. In this partial setoid, none of the terms are defined,
 because reflexivity never holds. As such, this gives the initial object.


 Content
 1. The initial partial setoid
 2. The morphism from the initial partial setoid and its uniqueness
 3. The initial object
 4. This initial object is strict

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.

Local Open Scope cat.
Local Open Scope hd.

Section PartialEquivalenceRelationInitial.
  Context (H : first_order_hyperdoctrine).

  (** * 1. The initial partial setoid *)
  Proposition bot_partial_setoid_axioms
    : @per_axioms H 𝟙 ⊥.
  Proof.
    split.
    - unfold per_symm_axiom.
      hypersimplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      hypersimplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition bot_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact 𝟙.
    - use make_per.
      + exact ⊥.
      + exact bot_partial_setoid_axioms.
  Defined.

  Proposition eq_in_bot_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ bot_partial_setoid}
              (p : Δ ⊢ ⊥)
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    hypersimplify.
    exact p.
  Qed.

  Proposition from_eq_in_bot_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ bot_partial_setoid}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ⊥.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    hypersimplify.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 2. The morphism from the initial partial setoid and its uniqueness *)
  Proposition bot_partial_setoid_morphism_laws
              (X : partial_setoid H)
    : @partial_setoid_morphism_laws H bot_partial_setoid X ⊥.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn.
      hypersimplify.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn.
      hypersimplify.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      cbn.
      hypersimplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      cbn.
      hypersimplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      cbn.
      hypersimplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      unfold partial_setoid_formula ; cbn.
      hypersimplify.
      use false_elim.
      apply hyperdoctrine_hyp.
  Qed.

  Definition bot_partial_setoid_morphism
             (X : partial_setoid H)
    : partial_setoid_morphism bot_partial_setoid X.
  Proof.
    use make_partial_setoid_morphism.
    - exact ⊥.
    - exact (bot_partial_setoid_morphism_laws X).
  Defined.

  Proposition bot_partial_setoid_morphism_eq
              {X : partial_setoid H}
              (f : partial_setoid_morphism bot_partial_setoid X)
    : f = bot_partial_setoid_morphism X.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - refine (hyperdoctrine_cut
                (partial_setoid_mor_dom_defined f (π₁ (tm_var _)) (π₂ (tm_var _)) _)
                _).
      + cbn.
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + exact (from_eq_in_bot_partial_setoid (hyperdoctrine_hyp _)).
    - use false_elim.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The initial object *)
  Definition initial_partial_setoid
    : Initial (category_of_partial_setoids H).
  Proof.
    use make_Initial.
    - exact bot_partial_setoid.
    - intros X.
      use make_iscontr.
      + exact (bot_partial_setoid_morphism X).
      + exact bot_partial_setoid_morphism_eq.
  Defined.

  (** * 4. This initial object is strict *)
  Proposition bot_partial_setoid_morphism_eq_id
              {X : partial_setoid H}
              (φ : partial_setoid_morphism X bot_partial_setoid)
    : partial_setoid_comp_morphism φ (bot_partial_setoid_morphism X)
      =
      id_partial_setoid_morphism X.
  Proof.
    use eq_partial_setoid_morphism.
    - cbn.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      hypersimplify_form.
      use false_elim.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - cbn.
      use exists_intro.
      + exact !!.
      + hypersimplify.
        use false_elim.
        pose (x₁ := π₁ (tm_var (X ×h X))).
        pose (x₂ := π₂ (tm_var (X ×h X))).
        fold x₁ x₂.
        use (exists_elim (partial_setoid_mor_hom_exists φ _)).
        * exact x₁.
        * exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
        * unfold x₁, x₂ ; clear x₁ x₂.
          hypersimplify.
          cbn.
          pose (x₁ := π₁ (π₁ (tm_var ((X ×h X) ×h 𝟙)))).
          pose (x₂ := π₂ (π₁ (tm_var ((X ×h X) ×h 𝟙)))).
          pose (y := π₂ (tm_var ((X ×h X) ×h 𝟙))).
          fold x₁ x₂ y.
          use from_eq_in_bot_partial_setoid.
          ** exact y.
          ** exact y.
          ** use (partial_setoid_mor_cod_defined φ x₁ y).
             use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  Definition is_strict_initial_parital_setoid
    : is_strict_initial initial_partial_setoid.
  Proof.
    intros X φ.
    use make_is_z_isomorphism.
    - exact (bot_partial_setoid_morphism X).
    - abstract
        (split ;
         [ apply bot_partial_setoid_morphism_eq_id
         | apply InitialArrowEq ]).
  Defined.
End PartialEquivalenceRelationInitial.
