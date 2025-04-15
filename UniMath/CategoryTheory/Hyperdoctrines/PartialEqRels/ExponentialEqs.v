(******************************************************************************************

 Equalities of exponentials of partial setoids

 Our goal is to prove that the category of partial setoids in a tripos is a topos, and for
 that we need to show that it has exponentials. We already constructed the object of the
 exponential and the evaluation and lambda abstraction morphisms. In this file, we finish
 the construction by verifying the necessary equalities. The two equalities that we need
 to verify are the following:
 - The beta-rule. The evaluation and lambda abstraction map need to satisfy the beta-rule,
   which can be expressed as the commutativity of a diagram.
 - The eta-rule. Lambda abstraction gives the unique morphism making some diagram commute.

 We start with some preliminary material. To prove the beta-rule and the eta-rule, we need to
 deal with statements that express the commutativity of some diagram, which says some morphism
 defined by [partial_setoid_exp_comm] is equal to some [φ]. Our first goal is to simplify such
 statements, so that proving and using them becomes more convenient.

 Content
 1. Basic material that is useful in the remainder of the file
 2. The beta-rule
 3. The eta-rule

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
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialEval.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialLam.

Local Open Scope cat.
Local Open Scope hd.

Section HelpEquality.
  Context {H : tripos}
          {X Y Z : partial_setoid H}
          (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y)
          (ψ : partial_setoid_morphism Z (exp_partial_setoid X Y)).

  (** * 1. Basic material that is useful in the remainder of the file *)
  Definition partial_setoid_exp_comm
    : partial_setoid_morphism (prod_partial_setoid X Z) Y
    := partial_setoid_comp_morphism
         (pair_partial_setoid_morphism
            (partial_setoid_comp_morphism
               (partial_setoid_pr1 X Z)
               (id_partial_setoid_morphism X))
            (partial_setoid_comp_morphism
               (partial_setoid_pr2 X Z)
               ψ))
         (eval_partial_setoid X Y).

  Let ζ : partial_setoid_morphism (prod_partial_setoid X Z) Y
    := partial_setoid_exp_comm.

  Definition exp_comm_partial_setoid_1
    : form (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y))
    := let x := π₁ (π₂ (tm_var (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)))) in
       let x' := π₁ (π₁ (π₁ (tm_var (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y))))) in
       let y := π₂ (π₁ (tm_var (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)))) in
       let z := π₂ (π₁ (π₁ (tm_var (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y))))) in
       let f := π₂ (π₂ (tm_var (((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)))) in
       exp_partial_setoid_is_function [ f ]
       ∧
       ⟨ x , y ⟩ ∈ f.

  Definition exp_comm_partial_setoid_2
    : form ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z)
    := let x := π₁ (π₂ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z)))) in
       let x' := π₁ (π₁ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z))))) in
       let y := π₂ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z)))) in
       let z := π₂ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z)) in
       let z' := π₂ (π₁ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z))))) in
       let f := π₂ (π₂ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h Z)))) in
       x' ~ x'
       ∧
       z' ~ z
       ∧
       ψ [ ⟨ z , f ⟩].

  Definition exp_comm_partial_setoid_3
    : form ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X)
    := let x := π₂ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X)) in
       let x' := π₁ (π₂ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X)))) in
       let x'' := π₁ (π₁ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X))))) in
       let y := π₂ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X)))) in
       let z := π₂ (π₁ (π₁ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X))))) in
       let f := π₂ (π₂ (π₁ (tm_var ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X)))) in
       x'' ~ x
       ∧
       z ~ z
       ∧
       x ~ x'.

  Definition exp_comm_partial_setoid
    : form (prod_partial_setoid X Z ×h Y)
    := ∃h ((∃h exp_comm_partial_setoid_3)
           ∧
           (∃h exp_comm_partial_setoid_2)
           ∧
           exp_comm_partial_setoid_1).

  Proposition exp_comm_partial_setoid_eq
    : exp_comm_partial_setoid = ζ.
  Proof.
    refine (!_).
    cbn.
    hypersimplify.
    unfold eval_partial_setoid_form.
    hypersimplify.
    rewrite !conj_assoc.
    reflexivity.
  Qed.

  Proposition to_exp_comm_partial_setoid
              (Δ : form ((X ×h Z) ×h Y))
              (x := π₁ (π₁ (tm_var ((X ×h Z) ×h Y))))
              (y := π₂ (tm_var ((X ×h Z) ×h Y)))
              (z := π₂ (π₁ (tm_var ((X ×h Z) ×h Y))))
              (t₁ t₂ : tm ((X ×h Z) ×h Y) X)
              (t₃ : tm ((X ×h Z) ×h Y) Z)
              (f : tm ((X ×h Z) ×h Y) (ℙ (X ×h Y)))
              (p₁ : Δ ⊢ x ~ t₂)
              (p₂ : Δ ⊢ z ~ z)
              (p₃ : Δ ⊢ t₂ ~ t₁)
              (p₄ : Δ ⊢ z ~ t₃)
              (p₅ : Δ ⊢ ψ [⟨ t₃ , f ⟩])
              (p₆ : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (p₇ : Δ ⊢ ⟨ t₁, y ⟩ ∈ f)
    : Δ ⊢ exp_comm_partial_setoid.
  Proof.
    cbn in Δ.
    use exists_intro.
    {
      exact ⟨ t₁ , f ⟩.
    }
    hypersimplify 0.
    repeat use conj_intro.
    - use exists_intro.
      {
        exact t₂.
      }
      unfold exp_comm_partial_setoid_3.
      cbn.
      hypersimplify 0.
      rewrite !partial_setoid_subst.
      simplify.
      fold x y z.
      repeat use conj_intro.
      + exact p₁.
      + exact p₂.
      + exact p₃.
    - use exists_intro.
      {
        exact t₃.
      }
      unfold exp_comm_partial_setoid_2.
      hypersimplify 0.
      rewrite !partial_setoid_subst.
      simplify.
      fold x y z.
      repeat use conj_intro.
      + exact (partial_setoid_refl_l p₁).
      + exact p₄.
      + exact p₅.
    - unfold exp_comm_partial_setoid_1.
      simplify.
      fold y.
      repeat use conj_intro.
      + exact p₆.
      + exact p₇.
  Qed.

  Proposition from_exp_comm_partial_setoid
              (χ : form ((X ×h Z) ×h Y))
              (Γ := ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X) ×h Z)
              (x₁ := π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))
              (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ)))))
              (x₃ := π₂ (π₁ (tm_var Γ)))
              (y := π₂ (π₁ (π₁ (π₁ (tm_var Γ)))))
              (z₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))
              (z₂ := π₂ (tm_var Γ))
              (f := π₂ (π₂ (π₁ (π₁ (tm_var Γ)))))
              (p : (exp_comm_partial_setoid_1 [ ⟨ ⟨ ⟨ x₁ , z₁ ⟩ , y ⟩ , ⟨ x₂ , f ⟩ ⟩ ]
                    ∧
                    exp_comm_partial_setoid_3 [ ⟨ ⟨ ⟨ ⟨ x₁ , z₁ ⟩ , y ⟩ , ⟨ x₂ , f ⟩ ⟩ , x₃ ⟩ ]
                    ∧
                    exp_comm_partial_setoid_2 [ ⟨ ⟨ ⟨ ⟨ x₁ , z₁ ⟩ , y ⟩ , ⟨ x₂ , f ⟩ ⟩ , z₂ ⟩ ]
                   ⊢
                   χ [ ⟨ ⟨ x₁ , z₁ ⟩ , y ⟩ ]))
    : exp_comm_partial_setoid ⊢ χ.
  Proof.
    unfold exp_comm_partial_setoid.
    use (exists_elim (hyperdoctrine_hyp _)).
    use weaken_right.
    pose (Δ := (∃h exp_comm_partial_setoid_3
                ∧
                ∃h exp_comm_partial_setoid_2
                ∧
                exp_comm_partial_setoid_1)).
    assert (Δ ⊢ ∃h exp_comm_partial_setoid_3) as q.
    {
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    unfold Δ in q.
    use (exists_elim q) ; clear q.
    hypersimplify 0.
    use hyp_ltrans.
    use weaken_right.
    use hyp_ltrans.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    hypersimplify 0.
    use hyp_ltrans.
    use weaken_right.
    simplify.
    refine (hyperdoctrine_cut
              (hyperdoctrine_cut _ p)
              _).
    - fold Γ.
      use hyp_ltrans.
      unfold x₁, x₂, x₃, y, z₁, z₂, f.
      rewrite <- !hyperdoctrine_pair_eta.
      apply hyperdoctrine_hyp.
    - fold Γ.
      unfold x₁, z₁, y.
      rewrite <- !hyperdoctrine_pair_eta.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition from_exp_comm_partial_setoid_weaken
              {Γ : ty H}
              (Δ χ : form Γ)
              (γ : tm Γ (prod_partial_setoid X Z ×h Y))
              (Γ' := ((Γ ×h X ×h ℙ (X ×h Y)) ×h X) ×h Z)
              (x₁ := π₁ (π₂ (π₁ (π₁ (tm_var Γ')))))
              (x₂ := π₂ (π₁ (tm_var Γ')))
              (z := π₂ (tm_var Γ'))
              (δ := π₁ (π₁ (π₁ (tm_var Γ'))))
              (f := π₂ (π₂ (π₁ (π₁ (tm_var Γ')))))
              (p : Δ [δ]
                   ∧ exp_comm_partial_setoid_1 [⟨ γ [δ ]tm, ⟨ x₁ , f ⟩ ⟩]
                   ∧ exp_comm_partial_setoid_3 [⟨ ⟨ γ [δ ]tm, ⟨ x₁ , f ⟩ ⟩, x₂ ⟩]
                   ∧ exp_comm_partial_setoid_2 [⟨ ⟨ γ [δ ]tm, ⟨ x₁ , f ⟩ ⟩, z ⟩]
                   ⊢
                   χ [δ])
    : Δ ∧ exp_comm_partial_setoid [ γ ] ⊢ χ.
  Proof.
    unfold exp_comm_partial_setoid.
    rewrite !exists_subst.
    refine (exists_elim _ _).
    {
      use weaken_right.
      apply hyperdoctrine_hyp.
    }
    rewrite !conj_subst.
    use hyp_sym.
    use hyp_rtrans.
    use weaken_left.
    use hyp_sym.
    rewrite !exists_subst.
    refine (exists_elim _ _).
    {
      use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    rewrite !conj_subst.
    refine (exists_elim _ _).
    {
      use weaken_left.
      do 2 use weaken_right.
      use weaken_left.
      rewrite exists_subst.
      apply hyperdoctrine_hyp.
    }
    rewrite !conj_subst.
    refine (hyperdoctrine_cut _ (hyperdoctrine_cut p _)).
    - repeat use conj_intro.
      + do 3 use weaken_left.
        simplify.
        apply hyperdoctrine_hyp.
      + do 2 use weaken_left.
        do 3 use weaken_right.
        simplify.
        unfold x₁, f.
        rewrite <- hyperdoctrine_pair_eta.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        unfold x₁, f.
        rewrite <- hyperdoctrine_pair_eta.
        simplify.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        unfold x₁, f.
        rewrite <- hyperdoctrine_pair_eta.
        simplify.
        apply hyperdoctrine_hyp.
    - simplify.
      apply hyperdoctrine_hyp.
  Qed.
End HelpEquality.

Section LamEqs.
  Context {H : tripos}
          {X Y Z : partial_setoid H}
          (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

  (** * 2. The beta-rule *)
  Let ζ : partial_setoid_morphism (prod_partial_setoid X Z) Y
    := partial_setoid_exp_comm (lam_partial_setoid φ).

  Definition lam_partial_setoid_comm_form
             (x := π₁ (π₁ (π₂ (tm_var ((X ×h Y) ×h (X ×h Z) ×h Y)))))
             (y := π₂ (π₂ (tm_var ((X ×h Y) ×h (X ×h Z) ×h Y))))
             (z := π₂ (π₁ (π₂ (tm_var ((X ×h Y) ×h (X ×h Z) ×h Y)))))
    : tm ((X ×h Z) ×h Y) (ℙ (X ×h Y))
    := {{ lam_image_form φ }} [ ⟨ !! , π₂ (π₁ (tm_var _)) ⟩ ]tm.

  Proposition is_function_lam_partial_setoid_comm_form
    : φ ⊢ exp_partial_setoid_is_function [ lam_partial_setoid_comm_form ].
  Proof.
    unfold lam_partial_setoid_comm_form.
    use (hyperdoctrine_cut
           _
           (hyperdoctrine_cut
              (hyperdoctrine_proof_subst
                 ⟨ !! , π₂ (π₁ (tm_var _)) ⟩
                 (is_function_lam_image_form φ _ (hyperdoctrine_hyp _)))
              _)).
    - rewrite partial_setoid_subst.
      simplify.
      pose (x := π₁ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      pose (y := π₂ (tm_var ((X ×h Z) ×h Y))).
      pose (z := π₂ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      fold z.
      refine (hyperdoctrine_cut
                (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y _)
                _).
      + unfold x, y, z.
        rewrite <- !hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_cut
                  (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _))
                  _).
        simplify.
        apply hyperdoctrine_hyp.
    - simplify.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition lam_partial_setoid_eq_lam_partial_setoid_comm_form
              (z := π₂ (π₁ (tm_var ((X ×h Z) ×h Y))))
    : φ ⊢ (lam_partial_setoid_eq φ) [⟨ z , lam_partial_setoid_comm_form ⟩].
  Proof.
    unfold lam_partial_setoid_comm_form.
    simple refine (hyperdoctrine_cut
                     _
                     (hyperdoctrine_cut
                        (hyperdoctrine_proof_subst
                           ⟨ !! , π₂ (π₁ (tm_var _)) ⟩
                           (lam_partial_setoid_eq_image_form
                              φ
                              (π₂ (tm_var _) ~ π₂ (tm_var _))))
                        _)).
    - clear z.
      rewrite partial_setoid_subst.
      simplify.
      pose (x := π₁ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      pose (y := π₂ (tm_var ((X ×h Z) ×h Y))).
      pose (z := π₂ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      fold z.
      refine (hyperdoctrine_cut
                (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y _)
                _).
      + unfold x, y, z.
        rewrite <- !hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_cut
                  (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _))
                  _).
        simplify.
        apply hyperdoctrine_hyp.
    - simplify.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition lam_partial_setoid_comm
    : φ = ζ.
  Proof.
    use eq_partial_setoid_morphism.
    - unfold ζ.
      rewrite <- exp_comm_partial_setoid_eq.
      pose (x := π₁ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      pose (y := π₂ (tm_var ((X ×h Z) ×h Y))).
      pose (z := π₂ (π₁ (tm_var ((X ×h Z) ×h Y)))).
      assert (φ ⊢ x ~ x) as p₁.
      {
        refine (hyperdoctrine_cut
                  (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y _)
                  _).
        {
          unfold x, y, z.
          rewrite <- !hyperdoctrine_pair_eta.
          rewrite hyperdoctrine_id_subst.
          apply hyperdoctrine_hyp.
        }
        use eq_in_prod_partial_setoid_l.
        unfold x, z.
        rewrite <- hyperdoctrine_pair_eta.
        apply hyperdoctrine_hyp.
      }
      assert (φ ⊢ z ~ z) as p₂.
      {
        refine (hyperdoctrine_cut
                  (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y _)
                  _).
        {
          unfold x, y, z.
          rewrite <- !hyperdoctrine_pair_eta.
          rewrite hyperdoctrine_id_subst.
          apply hyperdoctrine_hyp.
        }
        use eq_in_prod_partial_setoid_r.
        unfold x, z.
        rewrite <- hyperdoctrine_pair_eta.
        apply hyperdoctrine_hyp.
      }
      use to_exp_comm_partial_setoid.
      + exact x.
      + exact x.
      + exact z.
      + exact lam_partial_setoid_comm_form.
      + fold x.
        exact p₁.
      + fold z.
        exact p₂.
      + exact p₁.
      + fold z.
        exact p₂.
      + cbn.
        unfold lam_partial_setoid_form.
        hypersimplify 0.
        use conj_intro.
        * unfold lam_partial_setoid_is_def.
          hypersimplify 0.
          rewrite partial_setoid_subst.
          simplify.
          repeat use conj_intro.
          ** exact p₂.
          ** apply is_function_lam_partial_setoid_comm_form.
        * apply lam_partial_setoid_eq_lam_partial_setoid_comm_form.
      + apply is_function_lam_partial_setoid_comm_form.
      + unfold lam_partial_setoid_comm_form.
        fold y z.
        rewrite lam_image_form_eq.
        unfold x, y, z.
        rewrite <- !hyperdoctrine_pair_eta.
        simplify.
        apply hyperdoctrine_hyp.
    - unfold ζ.
      rewrite <- exp_comm_partial_setoid_eq.
      use from_exp_comm_partial_setoid.
      pose (Γ := ((((X ×h Z) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X) ×h Z).
      pose (x₁ := π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      pose (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ))))).
      pose (x₃ := π₂ (π₁ (tm_var Γ))).
      pose (y := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      pose (z₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      pose (z₂ := π₂ (tm_var Γ)).
      pose (f := π₂ (π₂ (π₁ (π₁ (tm_var Γ))))).
      unfold Γ in *.
      fold x₁ x₂ x₃ y z₁ z₂ f.
      match goal with
      | [ |- ?Δ' ⊢ _ ] => pose (Δ := Δ')
      end.
      fold Δ.
      assert (Δ ⊢ ⟨ x₂ , y ⟩ ∈ f) as p₁.
      {
        use weaken_left.
        unfold exp_comm_partial_setoid_1.
        simplify.
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      assert (Δ ⊢ x₁ ~ x₂) as p₂.
      {
        use weaken_right.
        use weaken_left.
        unfold exp_comm_partial_setoid_3.
        hypersimplify 0.
        rewrite !partial_setoid_subst.
        simplify.
        use partial_setoid_trans.
        + exact x₃.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_right.
          apply hyperdoctrine_hyp.
      }
      assert (Δ ⊢ exp_partial_setoid_is_function [f]) as p₃.
      {
        use weaken_left.
        unfold exp_comm_partial_setoid_1.
        simplify.
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      assert (Δ ⊢ ⟨ x₁ , y ⟩ ∈ f) as p₄.
      {
        use exp_partial_setoid_eq_defined.
        + exact p₃.
        + exact x₂.
        + use partial_setoid_sym.
          exact p₂.
        + exact y.
        + exact (exp_partial_setoid_cod_defined _ _ p₃ p₁).
        + exact p₁.
      }
      assert (Δ ⊢ φ [⟨ ⟨ x₁ , z₂ ⟩ , y ⟩] ⇔ ⟨ x₁ , y ⟩ ∈ f) as p₅.
      {
        do 2 use weaken_right.
        unfold exp_comm_partial_setoid_2.
        rewrite !conj_subst.
        do 2 use weaken_right.
        unfold lam_partial_setoid ; cbn.
        simplify.
        exact (lam_partial_setoid_eq_iff φ z₂ f (hyperdoctrine_hyp _) x₁ y).
      }
      assert (Δ ⊢ z₁ ~ z₂) as p₆.
      {
        do 2 use weaken_right.
        unfold exp_comm_partial_setoid_2.
        rewrite !conj_subst.
        hypersimplify 0.
        rewrite !partial_setoid_subst.
        simplify.
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      assert (Δ ⊢ φ [⟨ ⟨ x₁ , z₂ ⟩ , y ⟩]) as p₇.
      {
        use (iff_elim_right p₅).
        exact p₄.
      }
      refine (partial_setoid_mor_eq_defined φ _ _ p₇).
      + use eq_in_prod_partial_setoid.
        * simplify.
          exact (partial_setoid_refl_l p₂).
        * simplify.
          use partial_setoid_sym.
          exact p₆.
      + exact (exp_partial_setoid_cod_defined _ _ p₃ p₁).
  Qed.

  (** * 3. The eta-rule *)
  Context (φ' : partial_setoid_morphism Z (exp_partial_setoid X Y)).

  Let ζ' : partial_setoid_morphism (prod_partial_setoid X Z) Y
    := partial_setoid_exp_comm φ'.

  Context (p : φ = ζ').

  Lemma lam_partial_setoid_unique_left
    : φ' ⊢ lam_partial_setoid φ.
  Proof.
    rewrite p.
    cbn.
    pose (z := π₁ (tm_var (Z ×h exp_partial_setoid X Y))).
    pose (f := π₂ (tm_var (Z ×h exp_partial_setoid X Y))).
    rewrite <- (hyperdoctrine_id_subst (lam_partial_setoid_form ζ')).
    rewrite (hyperdoctrine_pair_eta (tm_var (Z ×h exp_partial_setoid X Y))).
    fold z f.
    use to_lam_partial_setoid_eq.
    - use (partial_setoid_mor_dom_defined φ' z f).
      unfold z, f.
      rewrite <- hyperdoctrine_pair_eta.
      simplify.
      apply hyperdoctrine_hyp.
    - assert (φ' ⊢ f ~ f) as q.
      {
        use (partial_setoid_mor_cod_defined φ' z f).
        unfold z, f.
        rewrite <- hyperdoctrine_pair_eta.
        simplify.
        apply hyperdoctrine_hyp.
      }
      refine (hyperdoctrine_cut q _).
      use from_eq_in_exp_partial_setoid_function_left.
      {
        exact f.
      }
      apply hyperdoctrine_hyp.
    - unfold lam_partial_setoid_eq.
      rewrite !forall_subst.
      do 2 use forall_intro.
      unfold z, f ; clear z f ; cbn -[ζ'].
      simplify.
      pose (x := π₂ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))).
      pose (y := π₂ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))).
      pose (z := π₁ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))))).
      pose (f := π₂ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))))).
      fold x y z f.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))))).
      fold z f.
      unfold ζ'.
      rewrite <- exp_comm_partial_setoid_eq.
      assert (φ' [⟨ z , f ⟩] ⊢ z ~ z) as q₁.
      {
        use (partial_setoid_mor_dom_defined φ' z f).
        apply hyperdoctrine_hyp.
      }
      assert (φ' [⟨ z , f ⟩] ⊢ exp_partial_setoid_is_function [ f ]) as q₂.
      {
        use from_eq_in_exp_partial_setoid_function_left.
        {
          exact f.
        }
        use (partial_setoid_mor_cod_defined φ' z f).
        apply hyperdoctrine_hyp.
      }
      assert (φ' [⟨ z , f ⟩] ∧ ⟨ x , y ⟩ ∈ f ⊢ x ~ x) as q₃.
      {
        use (exp_partial_setoid_dom_defined _ _ (weaken_left q₂ _)).
        {
          exact y.
        }
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      use iff_intro.
      + use from_exp_comm_partial_setoid_weaken.
        unfold x, y, z, f.
        clear x y z f q₁ q₂ q₃.
        cbn.
        simplify.
        pose (Γ' := (((((Z ×h ℙ (X ×h Y)) ×h X) ×h Y) ×h X ×h ℙ (X ×h Y)) ×h X) ×h Z).
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))).
        pose (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ'))))).
        pose (x₃ := π₂ (π₁ (tm_var Γ'))).
        pose (y := π₂ (π₁ (π₁ (π₁ (tm_var Γ'))))).
        pose (z₁ := π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))))).
        pose (z₂ := π₂ (tm_var Γ')).
        pose (f₁ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))))).
        pose (f₂ := π₂ (π₂ (π₁ (π₁ (tm_var Γ'))))).
        unfold Γ' in * ; clear Γ'.
        fold x₁ x₂ x₃ y z₁ z₂ f₁ f₂.
        unfold exp_comm_partial_setoid_1, exp_comm_partial_setoid_2, exp_comm_partial_setoid_3.
        hypersimplify 0.
        rewrite !partial_setoid_subst.
        simplify.
        pose (Δ := φ' [⟨ z₁, f₁ ⟩]
                   ∧ (exp_partial_setoid_is_function [f₂]
                      ∧ ⟨ x₂, y ⟩ ∈ f₂)
                   ∧ (x₁ ~ x₃ ∧ z₁ ~ z₁ ∧ x₃ ~ x₂)
                   ∧ x₁ ~ x₁
                   ∧ z₁ ~ z₂
                   ∧ φ' [⟨ z₂, f₂ ⟩]).
        assert (Δ ⊢ z₁ ~ z₂) as q₁.
        {
          do 4 use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ x₁ ~ x₂) as q₂.
        {
          do 2 use weaken_right.
          use weaken_left.
          use partial_setoid_trans.
          - exact x₃.
          - use weaken_left.
            apply hyperdoctrine_hyp.
          - do 2 use weaken_right.
            apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ exp_partial_setoid_is_function [f₂]) as q₃.
        {
          use weaken_right.
          do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ exp_partial_setoid_eq [⟨ f₂, f₁ ⟩]) as q₄.
        {
          use from_eq_in_exp_partial_setoid_function_eq.
          use (partial_setoid_mor_unique_im φ').
          - exact z₁.
          - use (partial_setoid_mor_eq_defined φ').
            + exact z₂.
            + exact f₂.
            + use partial_setoid_sym.
              exact q₁.
            + use eq_in_exp_partial_setoid.
              * exact q₃.
              * apply exp_partial_setoid_eq_refl.
            + do 5 use weaken_right.
              apply hyperdoctrine_hyp.
          - use weaken_left.
            apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ exp_partial_setoid_is_function [f₁]) as q₅.
        {
          use exp_partial_setoid_eq_is_function.
          - exact f₂.
          - exact q₄.
          - exact q₃.
        }
        assert (Δ ⊢ ⟨ x₂ , y ⟩ ∈ f₂) as q₆.
        {
          use weaken_right.
          use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        assert (Δ ⊢ y ~ y) as q₇.
        {
          exact (exp_partial_setoid_cod_defined _ _ q₃ q₆).
        }
        use (from_exp_partial_setoid_eq _ _ q₄).
        use (exp_partial_setoid_eq_defined _ _ q₃).
        * exact x₂.
        * use partial_setoid_sym.
          exact q₂.
        * exact y.
        * exact q₇.
        * exact q₆.
      + unfold exp_comm_partial_setoid.
        rewrite exists_subst.
        use exists_intro.
        {
          exact ⟨ x , f ⟩.
        }
        rewrite !conj_subst.
        repeat use conj_intro.
        * rewrite !exists_subst.
          use exists_intro.
          {
            exact x.
          }
          simplify.
          unfold exp_comm_partial_setoid_3.
          hypersimplify 0.
          rewrite !partial_setoid_subst.
          simplify.
          repeat use conj_intro.
          ** exact q₃.
          ** use weaken_left.
             exact q₁.
          ** exact q₃.
        * rewrite !exists_subst.
          use exists_intro.
          {
            exact z.
          }
          simplify.
          unfold exp_comm_partial_setoid_2.
          hypersimplify 0.
          rewrite !partial_setoid_subst.
          simplify.
          repeat use conj_intro.
          ** exact q₃.
          ** use weaken_left.
             exact q₁.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
        * simplify.
          unfold exp_comm_partial_setoid_1.
          simplify.
          use conj_intro.
          ** use weaken_left.
             exact q₂.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  Lemma lam_partial_setoid_unique_right
    : lam_partial_setoid φ ⊢ φ'.
  Proof.
    rewrite p.
    use (exists_elim (partial_setoid_mor_hom_exists φ' _)).
    - exact (π₁ (tm_var _)).
    - use (partial_setoid_mor_dom_defined (lam_partial_setoid ζ')).
      {
        exact (π₂ (tm_var _)).
      }
      rewrite <- hyperdoctrine_pair_eta.
      simplify.
      apply hyperdoctrine_hyp.
    - cbn.
      simplify.
      pose (z := π₁ (π₁ (tm_var ((Z ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (f := π₂ (π₁ (tm_var ((Z ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (g := π₂ (tm_var ((Z ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
      fold z f g.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var _))).
      fold z f.
      assert ((lam_partial_setoid_form ζ') [⟨ z , f ⟩] ∧ φ' [⟨ z , g ⟩] ⊢ z ~ z) as q₁.
      {
        use weaken_right.
        use (partial_setoid_mor_dom_defined φ' z g).
        apply hyperdoctrine_hyp.
      }
      use (partial_setoid_mor_eq_defined φ').
      + exact z.
      + exact g.
      + exact q₁.
      + use eq_in_exp_partial_setoid.
        * use weaken_right.
          refine (hyperdoctrine_cut _ _).
          {
            use (partial_setoid_mor_cod_defined φ' z g).
            apply hyperdoctrine_hyp.
          }
          exact (from_eq_in_exp_partial_setoid_function_left _ _ (hyperdoctrine_hyp _)).
        * unfold exp_partial_setoid_eq.
          rewrite !forall_subst.
          do 2 use forall_intro.
          unfold z, f, g.
          clear z f g q₁.
          simplify.
          pose (Γ := (((Z ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y).
          pose (x := π₂ (π₁ (tm_var Γ))).
          pose (y := π₂ (tm_var Γ)).
          pose (z := π₁ (π₁ (π₁ (π₁ (tm_var Γ))))).
          pose (f := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
          pose (g := π₂ (π₁ (π₁ (tm_var Γ)))).
          unfold Γ in * ; clear Γ.
          fold x y z f g.
          pose (Δ := (lam_partial_setoid_form ζ') [⟨ z, f ⟩] ∧ φ' [⟨ z, g ⟩]).
          assert (Δ ⊢ (lam_partial_setoid_form ζ') [⟨ z, f ⟩]) as q.
          {
            use weaken_left.
            apply hyperdoctrine_hyp.
          }
          refine (iff_trans _ (lam_partial_setoid_eq_iff _ _ _ q x y)).
          unfold Δ.
          unfold ζ'.
          rewrite <- exp_comm_partial_setoid_eq.
          use iff_intro.
          ** unfold exp_comm_partial_setoid.
             rewrite !exists_subst.
             use exists_intro.
             {
               exact ⟨ x , g ⟩.
             }
             rewrite !conj_subst.
             match goal with
             | [ |- ?Δ' ⊢ _ ] => pose (Δ'' := Δ')
             end.
             assert (Δ'' ⊢ z ~ z) as q₁.
             {
               unfold Δ''.
               use weaken_left.
               use weaken_right.
               use (partial_setoid_mor_dom_defined φ' z g).
               apply hyperdoctrine_hyp.
             }
             assert (Δ'' ⊢ exp_partial_setoid_is_function [g]) as q₂.
             {
               use weaken_left.
               use weaken_right.
               refine (hyperdoctrine_cut _ _).
               {
                 use (partial_setoid_mor_cod_defined φ' z g).
                 apply hyperdoctrine_hyp.
               }
               exact (from_eq_in_exp_partial_setoid_function_left _ _ (hyperdoctrine_hyp _)).
             }
             assert (Δ'' ⊢ x ~ x) as q₃.
             {
               use (exp_partial_setoid_dom_defined _ _ q₂).
               {
                 exact y.
               }
               use weaken_right.
               apply hyperdoctrine_hyp.
             }
             repeat use conj_intro.
             *** rewrite !exists_subst.
                 use exists_intro.
                 {
                   exact x.
                 }
                 simplify.
                 unfold exp_comm_partial_setoid_3.
                 hypersimplify 0.
                 rewrite !partial_setoid_subst.
                 simplify.
                 repeat use conj_intro.
                 **** exact q₃.
                 **** exact q₁.
                 **** exact q₃.
             *** rewrite !exists_subst.
                 use exists_intro.
                 {
                   exact z.
                 }
                 simplify.
                 unfold exp_comm_partial_setoid_2.
                 hypersimplify 0.
                 rewrite !partial_setoid_subst.
                 simplify.
                 repeat use conj_intro.
                 **** exact q₃.
                 **** exact q₁.
                 **** use weaken_left.
                      use weaken_right.
                      apply hyperdoctrine_hyp.
             *** unfold exp_comm_partial_setoid_1.
                 simplify.
                 use conj_intro.
                 **** exact q₂.
                 **** use weaken_right.
                      apply hyperdoctrine_hyp.
          ** clear Δ q.
             unfold x, y, z, f, g.
             use from_exp_comm_partial_setoid_weaken.
             cbn.
             simplify.
             clear x y z f g.
             pose (Γ := ((((((Z ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y) ×h X ×h ℙ (X ×h Y))
                           ×h X) ×h Z).
             pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
             pose (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ))))).
             pose (x₃ := π₂ (π₁ (tm_var Γ))).
             pose (y := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
             pose (z₁ := π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))))).
             pose (z₂ := π₂ (tm_var Γ)).
             pose (f₁ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))))).
             pose (f₂ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))).
             pose (f₃ := π₂ (π₂ (π₁ (π₁ (tm_var Γ))))).
             unfold Γ in *.
             fold x₁ x₂ x₃ y z₁ z₂ f₁ f₂ f₃.
             unfold exp_comm_partial_setoid_1.
             unfold exp_comm_partial_setoid_2.
             unfold exp_comm_partial_setoid_3.
             hypersimplify 0.
             rewrite !partial_setoid_subst.
             simplify.
             match goal with
             | [ |- ?Δ' ⊢ _ ] => pose (Δ := Δ')
             end.
             assert (Δ ⊢ x₁ ~ x₂) as q₁.
             {
               use partial_setoid_trans.
               - exact x₃.
               - do 2 use weaken_right.
                 do 2 use weaken_left.
                 apply hyperdoctrine_hyp.
               - do 2 use weaken_right.
                 use weaken_left.
                 do 2 use weaken_right.
                 apply hyperdoctrine_hyp.
             }
             assert (Δ ⊢ exp_partial_setoid_is_function [f₃]) as q₂.
             {
               use weaken_right.
               do 2 use weaken_left.
               apply hyperdoctrine_hyp.
             }
             assert (Δ ⊢ z₁ ~ z₂) as q₃.
             {
               do 4 use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
             }
             assert (Δ ⊢ exp_partial_setoid_eq[⟨ f₃ , f₂ ⟩]) as q₄.
             {
               use from_eq_in_exp_partial_setoid_function_eq.
               use (partial_setoid_mor_unique_im φ').
               - exact z₁.
               - use (partial_setoid_mor_eq_defined φ').
                 + exact z₂.
                 + exact f₃.
                 + use partial_setoid_sym.
                   exact q₃.
                 + use eq_in_exp_partial_setoid.
                   * exact q₂.
                   * apply exp_partial_setoid_eq_refl.
                 + do 5 use weaken_right.
                   apply hyperdoctrine_hyp.
               - use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
             }
             assert (Δ ⊢ ⟨ x₂, y ⟩ ∈ f₃) as q₅.
             {
               use weaken_right.
               use weaken_left.
               use weaken_right.
               apply hyperdoctrine_hyp.
             }
             assert (Δ ⊢ y ~ y) as q₆.
             {
               exact (exp_partial_setoid_cod_defined _ _ q₂ q₅).
             }
             use (from_exp_partial_setoid_eq _ _ q₄).
             use (exp_partial_setoid_eq_defined _ _ q₂).
             *** exact x₂.
             *** use partial_setoid_sym.
                 exact q₁.
             *** exact y.
             *** exact q₆.
             *** exact q₅.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition lam_partial_setoid_unique
    : φ' = lam_partial_setoid φ.
  Proof.
    use eq_partial_setoid_morphism.
    - exact lam_partial_setoid_unique_left.
    - exact lam_partial_setoid_unique_right.
  Qed.
End LamEqs.
