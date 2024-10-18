(******************************************************************************************

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
    etrans.
    {
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        unfold eval_partial_setoid_form.
        simplify.
        apply idpath.
      }
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      unfold lam_partial_setoid_form.
      simplify.
      apply idpath.
    }
    apply maponpaths.
    rewrite !conj_assoc.
    apply idpath.
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
    simplify_form.
    repeat use conj_intro.
    - use exists_intro.
      {
        exact t₂.
      }
      unfold exp_comm_partial_setoid_3.
      cbn.
      simplify_form.
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
      simplify_form.
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
    simplify_form.
    use hyp_ltrans.
    use weaken_right.
    use hyp_ltrans.
    use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
    simplify_form.
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
End HelpEquality.

Section LamEqs.
  Context {H : tripos}
          {X Y Z : partial_setoid H}
          (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

  (* generalize this by making the lam_partial_setoid arbitrary *)
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
        simplify_form.
        use conj_intro.
        * unfold lam_partial_setoid_is_def.
          simplify_form.
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
        simplify_form.
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
        simplify_form.
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

  Context (φ' : partial_setoid_morphism Z (exp_partial_setoid X Y))
          (p : φ
               =
               partial_setoid_comp_morphism
                 (pair_partial_setoid_morphism
                    (partial_setoid_comp_morphism
                         (partial_setoid_pr1 X Z)
                         (id_partial_setoid_morphism X))
                      (partial_setoid_comp_morphism
                         (partial_setoid_pr2 X Z)
                         φ'))
                   (eval_partial_setoid X Y)).

    (** * 4. Uniqueness *)
    Proposition lam_partial_setoid_unique
      : φ' = lam_partial_setoid φ.
    Proof.
      use eq_partial_setoid_morphism.
      - admit.
      - admit.
    Admitted.
End PERLambda.
