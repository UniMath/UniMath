(******************************************************************************************

 Implication

 In this file, we construct the conjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the implication, we reuse the implication of the
 first-order hyperdoctrine together with a suitable conjunction to guarantee that only
 defined elements satisfy the formula.

 Content
 1. The formula
 2. Elimination rule
 3. Introduction rule
 4. Stability under substitution
 5. Fiberwise exponentials

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Conjunction.

Local Open Scope cat.
Local Open Scope hd.

Section Connectives.
  Context (H : first_order_hyperdoctrine).

  Section Implication.
    Context {Γ : partial_setoid H}
            (ψ₁ ψ₂ : per_subobject Γ).

    (** * 1. The formula *)
    Let ζ : form Γ := let γ := tm_var Γ in (ψ₁ ⇒ ψ₂) ∧ γ ~ γ.

    Proposition per_subobject_impl_laws
      : per_subobject_laws ζ.
    Proof.
      unfold ζ.
      split.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        hypersimplify 0.
        hypersimplify.
        pose (γ := π₂ (tm_var (𝟙 ×h Γ))).
        fold γ.
        use weaken_right.
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        hypersimplify 0.
        hypersimplify.
        pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
        pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
        fold γ₁ γ₂.
        use conj_intro.
        + use impl_intro.
          use per_subobject_eq.
          * exact γ₁.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          * use impl_elim.
            ** exact (ψ₁ [ γ₁ ]).
            ** use per_subobject_eq.
               *** exact γ₂.
               *** use partial_setoid_sym.
                   do 2 use weaken_left.
                   apply hyperdoctrine_hyp.
               *** use weaken_right.
                   apply hyperdoctrine_hyp.
            ** use weaken_left.
               use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
        + use weaken_left.
          use partial_setoid_refl_r.
          * exact γ₁.
          * apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_impl
      : per_subobject Γ.
    Proof.
      use make_per_subobject.
      - exact ζ.
      - exact per_subobject_impl_laws.
    Defined.

    (** * 2. Elimination rule *)
    Proposition per_subobject_impl_elim
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          (per_subobject_conj H ψ₁ per_subobject_impl)
          ψ₂.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold ζ.
      hypersimplify 0.
      hypersimplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use per_subobject_eq.
      - exact γ₁.
      - use weaken_left.
        apply hyperdoctrine_hyp.
      - use impl_elim.
        + exact (ψ₁ [ γ₁ ]).
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
    Qed.

    (** * 3. Introduction rule *)
    Context {χ : per_subobject Γ}
            (p : per_subobject_mor_law
                   (id_partial_setoid_morphism Γ)
                   (per_subobject_conj H ψ₁ χ)
                   ψ₂).

    Proposition per_subobject_impl_intro
      : per_subobject_mor_law
          (id_partial_setoid_morphism Γ)
          χ
          per_subobject_impl.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn ; unfold ζ.
      hypersimplify 0.
      hypersimplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use conj_intro.
      - use impl_intro.
        use (per_subobject_mor p).
        + exact γ₁.
        + cbn.
          hypersimplify.
          do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + cbn.
          hypersimplify.
          use conj_intro.
          * use per_subobject_eq.
            ** exact γ₂.
            ** use partial_setoid_sym.
               do 2 use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
      - use weaken_left.
        use partial_setoid_refl_r.
        + exact γ₁.
        + apply hyperdoctrine_hyp.
    Qed.
  End Implication.

  (** * 4. Stability under substitution *)
  Proposition per_subobject_impl_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
              (ψ₁ ψ₂ : per_subobject Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_impl
           (per_subobject_subst s ψ₁)
           (per_subobject_subst s ψ₂))
        (per_subobject_subst
           s
           (per_subobject_impl ψ₁ ψ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use hyp_sym.
    cbn.
    hypersimplify 0.
    hypersimplify.
    simple refine (exists_elim (partial_setoid_mor_hom_exists s _) _).
    - exact (π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁)))).
    - use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - hypersimplify 0.
      hypersimplify.
      pose (γ₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
      pose (γ₁' := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
      pose (γ₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
      fold γ₁ γ₁' γ₂.
      use exists_intro.
      + exact γ₂.
      + hypersimplify 0.
        hypersimplify.
        fold γ₁' γ₂.
        repeat (use conj_intro).
        * use hyp_ltrans.
          use weaken_right.
          use partial_setoid_mor_eq_defined.
          ** exact γ₁.
          ** exact γ₂.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_cod_defined s γ₁).
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use impl_intro.
          do 3 use hyp_ltrans.
          refine (weaken_cut _ _).
          {
            use (impl_elim _ (weaken_left (hyperdoctrine_hyp _) _)).
            use (exists_intro).
            {
              exact γ₂.
            }
            hypersimplify.
            fold γ₁.
            do 3 use weaken_right.
            apply hyperdoctrine_hyp.
          }
          use hyp_ltrans.
          use weaken_right.
          use hyp_sym.
          use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
          rewrite conj_subst.
          use hyp_ltrans.
          use weaken_right.
          unfold γ₁, γ₁', γ₂ ; clear γ₁ γ₁' γ₂.
          hypersimplify 0.
          hypersimplify.
          pose (γ₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))))).
          pose (γ₁' := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
          pose (γ₂ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
          pose (γ₂' := π₂ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))).
          fold γ₁ γ₁' γ₂ γ₂'.
          use per_subobject_eq.
          ** exact γ₂'.
          ** use (partial_setoid_mor_unique_im s).
             *** exact γ₁.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 do 2 use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_right.
          use (partial_setoid_mor_cod_defined s).
          ** exact γ₁.
          ** apply hyperdoctrine_hyp.
  Qed.

  (** * 5. Fiberwise exponentials *)
  Definition fiberwise_exponentials_per_subobject
    : fiberwise_exponentials (fiberwise_binproducts_per_subobject H).
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_impl ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂.
      exact (per_subobject_impl_elim ψ₁ ψ₂).
    - intros Γ ψ₁ ψ₂ χ p.
      exact (per_subobject_impl_intro ψ₁ ψ₂ p).
    - intros Γ₁ Γ₂ s ψ₁ ψ₂.
      exact (per_subobject_impl_subst s ψ₁ ψ₂).
  Defined.
End Connectives.
