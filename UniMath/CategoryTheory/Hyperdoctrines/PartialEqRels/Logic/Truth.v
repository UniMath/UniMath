(******************************************************************************************

 The truth formula of partial setoids

 In this file, we construct the truth formula in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the truth formula, we take the whole set, so all
 elements that are defined (i.e. reflexive according to the partial equivalence relation).

 Content
 1. The formula
 2. Introduction rule
 3. Stability under substitution
 4. The fiberwise terminal object

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section TruthFormula.
  Context (H : first_order_hyperdoctrine).

  (** * 1. The formula *)
  Proposition per_subobject_truth_laws
              (Γ : partial_setoid H)
    : per_subobject_laws (tm_var Γ ~ tm_var Γ).
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      hypersimplify.
      pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
      pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
      fold γ₁ γ₂.
      use partial_setoid_refl_r.
      {
        exact γ₁.
      }
      use weaken_left.
      apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_truth
             (Γ : partial_setoid H)
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact (tm_var _ ~ tm_var _).
    - exact (per_subobject_truth_laws Γ).
  Defined.

  (** * 2. Introduction rule *)
  Proposition per_subobject_truth_intro
              {Γ : partial_setoid H}
              (φ : per_subobject Γ)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        φ
        (per_subobject_truth Γ).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    hypersimplify.
    pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h Γ)))).
    pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ) ×h Γ))).
    fold γ₁ γ₂.
    use partial_setoid_refl_r.
    {
      exact γ₁.
    }
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 3. Stability under substitution *)
  Proposition per_subobject_truth_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_truth Γ₁)
        (per_subobject_subst s (per_subobject_truth Γ₂)).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    hypersimplify.
    pose (γ₁ := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁)))).
    pose (γ₂ := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₁))).
    fold γ₁ γ₂.
    simple refine (exists_elim (partial_setoid_mor_hom_exists s _) _).
    - exact γ₂.
    - use weaken_left.
      use partial_setoid_refl_r.
      {
        exact γ₁.
      }
      apply hyperdoctrine_hyp.
    - unfold γ₁, γ₂ ; clear γ₁ γ₂.
      pose (γ₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
      pose (γ₂ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
      pose (γ₃ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
      rewrite exists_subst.
      use exists_intro.
      {
        exact γ₃.
      }
      hypersimplify_form.
      hypersimplify.
      fold γ₁ γ₂ γ₃.
      use conj_intro.
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use (partial_setoid_mor_cod_defined s).
        * exact γ₂.
        * apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The fiberwise terminal object *)
  Definition fiberwise_terminal_per_subobject
    : fiberwise_terminal (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - exact per_subobject_truth.
    - intros Γ φ.
      exact (per_subobject_truth_intro φ).
    - intros Γ₁ Γ₂ s.
      exact (per_subobject_truth_subst s).
  Defined.
End TruthFormula.
