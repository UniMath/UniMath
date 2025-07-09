(******************************************************************************************

 The falsity formula of partial setoids

 In this file, we construct the falsity formula in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. For the falsity formula, we use the bottom formula.

 Content
 1. The formula
 2. Elimination rule
 3. Stability under substitution
 4. The fiberwise initial object

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section FalsityFormula.
  Context (H : first_order_hyperdoctrine).

  (** * 1. The formula *)
  Proposition per_subobject_false_laws
              (Γ : partial_setoid H)
    : per_subobject_laws (⊥ : form Γ).
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      hypersimplify.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      do 2 use impl_intro.
      use weaken_right.
      use false_elim.
      hypersimplify.
      apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_false
             (Γ : partial_setoid H)
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact ⊥.
    - exact (per_subobject_false_laws Γ).
  Defined.

  (** * 2. Elimination rule *)
  Proposition per_subobject_false_elim
              {Γ : partial_setoid H}
              (φ : per_subobject Γ)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        (per_subobject_false Γ)
        φ.
  Proof.
    do 2 use forall_intro.
    do 2 use impl_intro.
    use weaken_right.
    cbn.
    use false_elim.
    hypersimplify.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 3. Stability under substitution *)
  Proposition per_subobject_false_subst
              {Γ₁ Γ₂ : partial_setoid H}
              (s : partial_setoid_morphism Γ₁ Γ₂)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ₁)
        (per_subobject_subst s (per_subobject_false Γ₂))
        (per_subobject_false Γ₁).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    cbn.
    use hyp_sym.
    rewrite !exists_subst.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    rewrite !conj_subst.
    use hyp_ltrans.
    use weaken_right.
    do 2 use weaken_right.
    hypersimplify.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The fiberwise initial object *)
  Definition fiberwise_initial_per_subobject
    : fiberwise_initial (disp_cat_per_subobject_cleaving H).
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - apply locally_prop_disp_cat_per_subobject.
    - exact per_subobject_false.
    - intros Γ φ.
      exact (per_subobject_false_elim φ).
    - intros Γ₁ Γ₂ s.
      exact (per_subobject_false_subst s).
  Defined.
End FalsityFormula.
