(******************************************************************************************

 Evaluation of functions of partial setoids

 We defined the function space of partial setoids, and the next step is to define the
 evaluation morphism. Suppose that we have partial setoids `X` and `Y`. The evaluation
 morphism goes from the product of `X` and the exponential of `X` and `Y` to `Y`, so its
 underlying formula takes terms `x : X`, `f : exp_partial_setoid X Y`, and `y : Y`, and
 these terms satisfy the relation if `f` is defined and `(x , y) ∈ f`. In essence, this
 means that `x` is sent to `y` by `f`, and thus this formula describes evaluation.

 Content
 1. The formula of the evaluation morphism
 2. The laws of the evaluation morphism
 3. The evaluation morphism

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.

Local Open Scope cat.
Local Open Scope hd.

Section PEREvaluation.
  Context {H : tripos}
          (X Y : partial_setoid H).

  (** * 1. The formula of the evaluation morphism *)
  Definition eval_partial_setoid_form
    : form (prod_partial_setoid X (exp_partial_setoid X Y) ×h Y)
    := let x := π₁ (π₁ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y))) in
       let f := π₂ (π₁ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y))) in
       let y := π₂ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y)) in
       (exp_partial_setoid_is_function [ f ])
       ∧
       ⟨ x , y ⟩ ∈ f.

  Arguments eval_partial_setoid_form /.

  (** * 2. The laws of the evaluation morphism *)
  Proposition eval_partial_setoid_laws
    : partial_setoid_morphism_laws eval_partial_setoid_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
      pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
      pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
      use eq_in_prod_partial_setoid ; cbn ; fold x y f.
      + use (exp_partial_setoid_dom_defined X Y).
        * exact f.
        * exact y.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use eq_in_exp_partial_setoid.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * apply exp_partial_setoid_eq_refl.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
      pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
      pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
      fold x y f.
      use (exp_partial_setoid_cod_defined X Y).
      + exact f.
      + exact x.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      hypersimplify.
      pose (Γ := (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y).
      pose (f := π₂ (π₂ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      pose (g := π₂ (π₂ (π₁ (π₁ (tm_var Γ))))).
      pose (x₁ := π₁ (π₂ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      pose (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ))))).
      pose (y₁ := π₂ (π₁ (tm_var Γ))).
      pose (y₂ := π₂ (tm_var Γ)).
      unfold Γ in * ; clear Γ.
      fold f g x₁ x₂ y₁ y₂.
      refine (weaken_cut _ _).
      {
        do 2 use weaken_left.
        exact (from_eq_in_prod_partial_setoid _ _ (hyperdoctrine_hyp _)).
      }
      cbn.
      fold x₁ x₂ f g.
      do 2 use hyp_ltrans.
      use weaken_right.
      repeat use conj_intro.
      + use exp_partial_setoid_eq_is_function.
        * exact f.
        * use from_eq_in_exp_partial_setoid_function_eq.
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          do 2 use weaken_left.
          apply hyperdoctrine_hyp.
      + use exp_partial_setoid_eq_defined.
        * use from_eq_in_exp_partial_setoid_function_right.
          {
            exact f.
          }
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
        * exact x₁.
        * do 2 use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * exact y₁.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use from_exp_partial_setoid_eq.
          ** exact f.
          ** use from_eq_in_exp_partial_setoid_function_eq.
             do 3 use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law ; cbn.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      hypersimplify.
      pose (x := π₁ (π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))))).
      pose (f := π₂ (π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))))).
      pose (y := π₂ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))).
      pose (y' := π₂ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y))).
      fold x f y y'.
      use (exp_partial_setoid_unique_im X Y).
      + exact f.
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + exact x.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      pose (x := π₁ (π₂ (tm_var (𝟙 ×h X ×h ℙ (X ×h Y))))).
      pose (f := π₂ (π₂ (tm_var (𝟙 ×h X ×h ℙ (X ×h Y))))).
      use (hyperdoctrine_cut
             (from_eq_in_prod_partial_setoid _ _ (hyperdoctrine_hyp _))).
      cbn.
      fold x f.
      refine (hyperdoctrine_cut _ _).
      {
        refine (conj_intro (weaken_left (hyperdoctrine_hyp _) _) _).
        use weaken_right.
        exact (from_eq_in_exp_partial_setoid X Y (hyperdoctrine_hyp _)).
      }
      use (exists_elim (exp_partial_setoid_im_exists X Y _ _)).
      + exact f.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + exact x.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + unfold x, f ; clear x f.
        hypersimplify 0.
        hypersimplify.
        pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
        fold x f y.
        use exists_intro.
        * exact y.
        * hypersimplify.
          fold x f.
          repeat use conj_intro.
          ** use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The evaluation morphism *)
  Definition eval_partial_setoid
    : partial_setoid_morphism
        (prod_partial_setoid X (exp_partial_setoid X Y))
        Y.
  Proof.
    use make_partial_setoid_morphism.
    - exact eval_partial_setoid_form.
    - exact eval_partial_setoid_laws.
  Defined.
End PEREvaluation.
