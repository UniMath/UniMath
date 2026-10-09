(*********************************************************************************************

 The first-order hyperdoctrine of partial setoids

 Every first-order hyperdoctrine gives rise to the category of partial setoids in that
 first-order hyperdoctrine. The category of partial setoids enjoys many properties, and these
 allow us to interpret first-order predicate logic via partial setoids using monomorphisms. In
 this file, we construct an equivalent first-order hyperdoctrine that uses a simpler
 characterization of monomorphisms, namely as formulas in the original hyperdoctrine that
 satisfy some extra properties. This allows us to work with the internal logic in the same way
 as we use subsets. We also show that this first-order hyperdoctrine forms a tripos.

 Content
 1. The hyperdoctrine of PERs
 2. The first-order hyperdoctrine of PERs
 3. The tripos of PERs

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrineChosen.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERExponentials.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERSubobjectClassifier.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.MonoEquiv.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Truth.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Falsity.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Conjunction.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Disjunction.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Implication.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Existential.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Universal.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.Equality.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. The hyperdoctrine of PERs *)
Definition per_subobject_hyperdoctrine
           (H : first_order_hyperdoctrine)
  : hyperdoctrine.
Proof.
  use make_hyperdoctrine.
  - exact (category_of_partial_setoids H).
  - exact (disp_cat_per_subobject H).
  - exact (terminal_partial_setoid H).
  - exact (binproducts_partial_setoid H).
  - exact (disp_cat_per_subobject_cleaving H).
  - apply locally_prop_disp_cat_per_subobject.
  - apply is_univalent_disp_cat_per_subobject.
Defined.

(** * 2. The first-order hyperdoctrine of PERs *)
Definition per_subobject_universal_quantifiers
           (H : first_order_hyperdoctrine)
  : universal_quantifiers (per_subobject_hyperdoctrine H).
Proof.
  use universal_quantifiers_from_chosen.
  use make_universal_quantifiers_chosen.
  - intros Γ A φ.
    exact (per_subobject_forall φ).
  - intros Γ A φ.
    exact (per_subobject_forall_elim φ).
  - intros Γ A φ ψ p.
    exact (per_subobject_forall_intro φ p).
  - intros Γ₁ Γ₂ A s φ.
    exact (per_subobject_forall_subst s φ).
Defined.

Definition per_subobject_existential_quantifiers
           (H : first_order_hyperdoctrine)
  : existential_quantifiers (per_subobject_hyperdoctrine H).
Proof.
  use existential_quantifiers_from_chosen.
  use make_existential_quantifiers_chosen.
  - intros Γ A φ.
    exact (per_subobject_exists φ).
  - intros Γ A φ.
    exact (per_subobject_exists_intro φ).
  - intros Γ A φ ψ p.
    exact (per_subobject_exists_elim φ ψ p).
  - intros Γ₁ Γ₂ A s φ.
    exact (per_subobject_exists_subst s φ).
Defined.

Definition per_subobject_equality_formulas
           (H : first_order_hyperdoctrine)
  : equality_formulas (per_subobject_hyperdoctrine H).
Proof.
  use make_equality_formulas.
  - intros A φ.
    exact (per_subobject_equality φ).
  - intros A φ.
    exact (per_subobject_equality_refl φ).
  - intros A φ ψ p.
    exact (per_subobject_equality_elim p).
Defined.

Definition per_subobject_first_order_hyperdoctrine
           (H : first_order_hyperdoctrine)
  : first_order_hyperdoctrine.
Proof.
  use make_first_order_hyperdoctrine.
  - exact (per_subobject_hyperdoctrine H).
  - apply fiberwise_terminal_per_subobject.
  - apply fiberwise_initial_per_subobject.
  - apply fiberwise_binproducts_per_subobject.
  - apply fiberwise_bincoproducts_per_subobject.
  - apply fiberwise_exponentials_per_subobject.
  - apply per_subobject_universal_quantifiers.
  - apply per_subobject_existential_quantifiers.
  - apply per_subobject_equality_formulas.
Defined.

Local Open Scope weak_tripos.

(** * 3. The tripos of PERs *)
Section Tripos.
  Context (H : weak_tripos).

  Let Omega : ty (per_subobject_first_order_hyperdoctrine H)
    := omega_partial_setoid H.

  Definition per_generic_predicate_in
    : form Omega
    := monic_to_per_subobject _ (omega_partial_setoid_true _).

  Definition per_mor_to_generic_predicate
             {Γ : ty (per_subobject_first_order_hyperdoctrine H)}
             (φ : form Γ)
    : tm Γ (omega_partial_setoid H)
    := subobject_classifier_partial_setoid_map
         _
         (per_subobject_to_monic _ φ).

  Proposition per_mor_to_generic_predicate_eq
              {Γ : ty (per_subobject_first_order_hyperdoctrine H)}
              (φ : form Γ)
    : φ = per_generic_predicate_in [ per_mor_to_generic_predicate φ ].
  Proof.
    use path_per_subobject.
    use hyperdoctrine_formula_eq.
    - cbn.
      cbn in Γ, φ.
      refine (exists_elim _ _).
      {
        use (weak_tripos_form_to_tm φ).
        exact (tm_var _).
      }
      hypersimplify.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      repeat use conj_intro.
      + pose (γ := π₁ (tm_var (Γ ×h Ω))).
        pose (ω := π₂ (tm_var (Γ ×h Ω))).
        fold γ ω.
        use weaken_left.
        refine (per_subobject_def _ _ _).
        apply hyperdoctrine_hyp.
      + use impl_intro.
        use hyp_sym.
        refine (exists_elim _ _).
        {
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        rewrite conj_subst.
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        pose (γ₁ := π₁ (π₁ (tm_var ((Γ ×h Ω) ×h Γ)))).
        pose (γ₂ := π₂ (tm_var ((Γ ×h Ω) ×h Γ))).
        pose (ω := π₂ (π₁ (tm_var ((Γ ×h Ω) ×h Γ)))).
        fold γ₁ γ₂ ω.
        refine (iff_elim_left _ _).
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
      + pose (γ := π₁ (tm_var (Γ ×h Ω))).
        pose (ω := π₂ (tm_var (Γ ×h Ω))).
        fold γ ω.
        use impl_intro.
        use exists_intro.
        {
          exact γ.
        }
        hypersimplify.
        fold γ.
        use conj_intro.
        * do 2 use weaken_left.
          refine (per_subobject_def _ _ _).
          apply hyperdoctrine_hyp.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
      + pose (γ := π₁ (tm_var (Γ ×h Ω))).
        pose (ω := π₂ (tm_var (Γ ×h Ω))).
        fold γ ω.
        use exists_intro.
        {
          exact !!.
        }
        hypersimplify.
        fold ω.
        refine (iff_elim_left _ _).
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - cbn.
      refine (exists_elim _ _).
      {
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      hypersimplify.
      use hyp_sym.
      refine (exists_elim _ _).
      {
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      use hyp_ltrans.
      use hyp_sym.
      use hyp_ltrans.
      refine (weaken_cut _ _).
      {
        refine (iff_elim_right _ _).
        {
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      use hyp_ltrans.
      use weaken_right.
      use hyp_sym.
      refine (exists_elim _ _).
      {
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      cbn in Γ, φ.
      pose (Δ := ((Γ ×h Ω) ×h 𝟙) ×h Γ).
      fold Δ.
      pose (γ₁ := π₂ (tm_var Δ)).
      pose (γ₂ := π₁ (π₁ (π₁ (tm_var Δ)))).
      pose (ω := π₂ (π₁ (π₁ (tm_var Δ)))).
      fold γ₁ γ₂ ω.
      use (per_subobject_eq φ).
      + exact γ₁.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + do 2 use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_generic_predicate
    : generic_predicate
        (per_subobject_first_order_hyperdoctrine H).
  Proof.
    use make_generic_predicate.
    - exact Omega.
    - exact per_generic_predicate_in.
    - intros Γ φ.
      simple refine (_ ,, _).
      + exact (per_mor_to_generic_predicate φ).
      + exact (per_mor_to_generic_predicate_eq φ).
  Defined.

  Definition per_subobject_tripos
    : tripos.
  Proof.
    use tripos_from_generic_predicate.
    - exact (per_subobject_first_order_hyperdoctrine H).
    - exact per_subobject_generic_predicate.
    - exact (exponentials_partial_setoid H).
  Defined.
End Tripos.
