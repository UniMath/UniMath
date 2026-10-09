(******************************************************************************************

 The universal quantifier

 In this file, we construct the conjunction in the category of partial setoids. Here we
 use the characterization of subobjects in terms of formulas as given in the file
 `SubobjectDispCat.v`.

 The construction of the connectives of subobjects of partial setoids is similar to how
 connectives are defined for subsets. Since we solely look at universal quantification
 along projections, we can reuse the universal quantifier in the hyperdoctrine.

 Content
 1. The formula
 2. The elimination rule
 3. The introduction rule
 4. Stability under substitution

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

Section Universal.
  Context {H : first_order_hyperdoctrine}
          {Γ A : partial_setoid H}
          (φ : per_subobject (prod_partial_setoid Γ A)).

  (** * 1. The formula *)
  Definition per_subobject_forall_form_all
    : form (Γ ×h A)
    := tm_var _ ~ tm_var _ ⇒ φ.

  Definition per_subobject_forall_form
    : form Γ
    := tm_var _ ~ tm_var _ ∧ (∀h per_subobject_forall_form_all).

  Arguments per_subobject_forall_form_all /.

  Proposition per_subobject_forall_laws
    : per_subobject_laws per_subobject_forall_form.
  Proof.
    split.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      unfold per_subobject_forall_form.
      hypersimplify_form.
      rewrite partial_setoid_subst.
      use weaken_left.
      hypersimplify.
      apply hyperdoctrine_hyp.
    - unfold per_subobject_forall_form.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      hypersimplify.
      use conj_intro.
      + use weaken_left.
        exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
      + use forall_intro.
        hypersimplify.
        pose (Γ' := ((𝟙 ×h Γ) ×h Γ) ×h A).
        pose (a := π₂ (tm_var Γ')).
        pose (γ₁ := π₂ (π₁ (tm_var Γ'))).
        pose (γ₂ := π₂ (π₁ (π₁ (tm_var Γ')))).
        use hyp_rtrans.
        use hyp_sym.
        refine (weaken_cut _ _).
        {
          refine (forall_elim _ a).
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        hypersimplify_form.
        use hyp_ltrans.
        use weaken_right.
        use impl_intro.
        hypersimplify.
        fold Γ' a γ₁ γ₂.
        use per_subobject_eq.
        * exact ⟨ γ₂ , a ⟩.
        * use eq_in_prod_partial_setoid.
          ** hypersimplify.
             do 3 use weaken_left.
             apply hyperdoctrine_hyp.
          ** hypersimplify.
             use weaken_right.
             refine (hyperdoctrine_cut _ _).
             {
               exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
             }
             hypersimplify.
             apply hyperdoctrine_hyp.
        * refine (impl_elim _ (weaken_left (weaken_right (hyperdoctrine_hyp _) _) _)).
          use eq_in_prod_partial_setoid.
          ** hypersimplify.
             do 2 use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** hypersimplify.
             use weaken_right.
             refine (hyperdoctrine_cut _ _).
             {
               exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
             }
             hypersimplify.
             apply hyperdoctrine_hyp.
  Qed.

  Definition per_subobject_forall
    : per_subobject Γ.
  Proof.
    use make_per_subobject.
    - exact per_subobject_forall_form.
    - exact per_subobject_forall_laws.
  Defined.

  Arguments per_subobject_forall_form /.

  (** * 2. The elimination rule *)
  Proposition per_subobject_forall_elim
    : per_subobject_mor_law
        (id_partial_setoid_morphism _)
        (per_subobject_subst
           (partial_setoid_comp_morphism
              (id_partial_setoid_morphism _)
              (partial_setoid_pr1 _ _))
           per_subobject_forall)
        φ.
  Proof.
    use per_subobject_mor_law_over_id.
    cbn.
    refine (exists_elim (hyperdoctrine_hyp _) _).
    use weaken_right.
    hypersimplify.
    refine (exists_elim _ _).
    {
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    rewrite conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    pose (Γ' := ((Γ ×h A) ×h Γ) ×h Γ ×h A).
    fold Γ'.
    pose (γ₃ := π₁ (π₂ (tm_var Γ'))).
    pose (a₂ := π₂ (π₂ (tm_var Γ'))).
    pose (γ₂ := π₂ (π₁ (tm_var Γ'))).
    pose (γ₁ := π₁ (π₁ (π₁ (tm_var Γ')))).
    pose (a₁ := π₂ (π₁ (π₁ (tm_var Γ')))).
    cbn.
    fold a₁ a₂ γ₁ γ₂ γ₃.
    rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var Γ')))).
    fold a₁ γ₁.
    rewrite (hyperdoctrine_pair_eta (π₂ (tm_var Γ'))).
    fold a₂ γ₃.
    refine (weaken_cut _ _).
    {
      refine (forall_elim _ a₁).
      use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    }
    hypersimplify.
    cbn.
    fold γ₂.
    simple refine (per_subobject_eq φ _ _).
    - exact ⟨ γ₂ , a₁ ⟩.
    - use weaken_left.
      use weaken_right.
      use eq_in_prod_partial_setoid.
      + hypersimplify.
        refine (partial_setoid_trans _ _ _).
        {
          use weaken_right.
          use weaken_left.
          use partial_setoid_sym.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        use partial_setoid_sym.
        refine (hyperdoctrine_cut _ _).
        {
          refine (eq_in_prod_partial_setoid_l _ _ _).
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        hypersimplify.
        refine (hyperdoctrine_cut _ _).
        {
          refine (eq_in_prod_partial_setoid_r _ _ _).
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        refine (partial_setoid_refl_l _).
        apply hyperdoctrine_hyp.
    - refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      use weaken_right.
      use eq_in_prod_partial_setoid.
      + hypersimplify.
        use weaken_right.
        use weaken_left.
        refine (partial_setoid_refl_r _).
        apply hyperdoctrine_hyp.
      + use weaken_left.
        hypersimplify.
        refine (hyperdoctrine_cut _ _).
        {
          refine (eq_in_prod_partial_setoid_r _ _ _).
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        refine (partial_setoid_refl_l _).
        apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The introduction rule *)
  Proposition per_subobject_forall_intro
              {ψ : per_subobject Γ}
              (p : per_subobject_mor_law
                     (id_partial_setoid_morphism _)
                     (per_subobject_subst
                        (partial_setoid_comp_morphism
                           (id_partial_setoid_morphism _)
                           (partial_setoid_pr1 _ _))
                        ψ)
                     φ)
    : per_subobject_mor_law
        (id_partial_setoid_morphism Γ)
        ψ
        per_subobject_forall.
  Proof.
    use per_subobject_mor_law_over_id.
    cbn.
    use conj_intro.
    - refine (per_subobject_def ψ _ _).
      hypersimplify.
      apply hyperdoctrine_hyp.
    - use forall_intro.
      use impl_intro.
      rewrite <- (hyperdoctrine_id_subst φ).
      use (per_subobject_mor_over_id p).
      cbn.
      hypersimplify.
      use exists_intro.
      {
        exact (π₁ (tm_var _)).
      }
      hypersimplify.
      use conj_intro.
      + use exists_intro.
        {
          exact (tm_var _).
        }
        hypersimplify.
        repeat use conj_intro.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          refine (hyperdoctrine_cut _ _).
          {
            refine (eq_in_prod_partial_setoid_l _ _ _).
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          refine (hyperdoctrine_cut _ _).
          {
            refine (eq_in_prod_partial_setoid_r _ _ _).
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        apply hyperdoctrine_hyp.
  Qed.
End Universal.

Arguments per_subobject_forall_form /.

(** * 4. Stability under substitution *)
Proposition per_subobject_forall_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : partial_setoid H}
            (s : partial_setoid_morphism Γ₁ Γ₂)
            (φ : per_subobject (prod_partial_setoid Γ₂ A))
  : per_subobject_mor_law
      (id_partial_setoid_morphism Γ₁)
      (per_subobject_forall
         (per_subobject_subst
            (pair_partial_setoid_morphism
               (partial_setoid_comp_morphism
                  (partial_setoid_pr1 Γ₁ A)
                  s)
               (partial_setoid_comp_morphism
                  (partial_setoid_pr2 Γ₁ A)
                  (id_partial_setoid_morphism A)))
            φ))
      (per_subobject_subst s (per_subobject_forall φ)).
Proof.
  do 2 use forall_intro.
  use impl_intro.
  use weaken_right.
  use impl_intro.
  cbn -[per_subobject_subst].
  refine (hyperdoctrine_cut _ _).
  {
    cbn -[per_subobject_subst].
    rewrite conj_subst.
    use hyp_rtrans.
    use hyp_sym.
    apply hyperdoctrine_hyp.
  }
  refine (exists_elim _ _).
  {
    refine (partial_setoid_mor_hom_exists s _).
    do 2 use weaken_right.
    hypersimplify.
    apply hyperdoctrine_hyp.
  }
  pose (∀h (per_subobject_forall_form_all
              (per_subobject_subst
                 (pair_partial_setoid_morphism
                    (partial_setoid_comp_morphism (partial_setoid_pr1 Γ₁ A) s)
                    (partial_setoid_comp_morphism (partial_setoid_pr2 Γ₁ A)
                       (id_partial_setoid_morphism A)))
                 φ)))
    as Δ.
  fold Δ.
  hypersimplify.
  cbn -[per_subobject_forall].
  hypersimplify.
  use exists_intro.
  {
    exact (π₂ (tm_var _)).
  }
  cbn.
  hypersimplify_form.
  repeat use conj_intro.
  - pose (γ₁ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
    pose (γ₂ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
    pose (γ₃ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
    cbn.
    fold γ₁ γ₂ γ₃.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    refine (partial_setoid_mor_eq_defined _ _ _ (weaken_right (hyperdoctrine_hyp _) _)).
    + do 2 use weaken_left.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
  - pose (γ₁ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))).
    pose (γ₂ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂)))).
    pose (γ₃ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂))))).
    cbn.
    fold γ₁ γ₂ γ₃.
    use hyp_ltrans.
    do 2 use weaken_right.
    hypersimplify.
    exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
  - use forall_intro.
    unfold per_subobject_forall_form_all.
    cbn.
    hypersimplify.
    use impl_intro.
    hypersimplify.
    do 2 use hyp_ltrans.
    refine (weaken_cut _ _).
    {
      refine (forall_elim _ _).
      {
        use weaken_left.
        unfold Δ.
        rewrite forall_subst.
        apply hyperdoctrine_hyp.
      }
      exact (π₂ (tm_var _)).
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    use hyp_sym.
    refine (weaken_cut _ _).
    {
      unfold per_subobject_forall_form_all.
      rewrite impl_subst.
      refine (impl_elim _ (weaken_left (hyperdoctrine_hyp _) _)).
      use hyp_rtrans.
      use weaken_right.
      hypersimplify.
      use eq_in_prod_partial_setoid.
      - hypersimplify.
        use weaken_left.
        refine (partial_setoid_mor_dom_defined s _ _ _).
        apply hyperdoctrine_hyp.
      - use weaken_right.
        hypersimplify.
        refine (hyperdoctrine_cut _ _).
        {
          exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    refine (exists_elim _ _).
    {
      use weaken_left.
      cbn.
      rewrite exists_subst.
      apply hyperdoctrine_hyp.
    }
    rewrite conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    use (per_subobject_eq φ _ (weaken_right (weaken_right (hyperdoctrine_hyp _) _) _)).
    use hyp_rtrans.
    use weaken_left.
    use hyp_sym.
    use hyp_ltrans.
    refine (exists_elim _ _).
    {
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    rewrite conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify_form.
    use hyp_ltrans.
    refine (exists_elim _ _).
    {
      use weaken_left.
      apply hyperdoctrine_hyp.
    }
    rewrite conj_subst.
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    clear Δ.
    pose (Δ := ((((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h A) ×h Γ₂ ×h A) ×h Γ₁) ×h A).
    fold Δ.
    pose (a₁ := π₂ (tm_var Δ)).
    pose (γ₁ := π₂ (π₁ (tm_var Δ))).
    pose (γ₂ := π₁ (π₂ (π₁ (π₁ (tm_var Δ))))).
    pose (a₂ := π₂ (π₂ (π₁ (π₁ (tm_var Δ))))).
    pose (a₃ := π₂ (π₁ (π₁ (π₁ (tm_var Δ))))).
    pose (γ₃ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Δ)))))).
    pose (γ₄ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Δ))))))).
    pose (γ₅ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Δ)))))))).
    fold a₁ γ₁ a₂ γ₂ a₃ γ₃ γ₄ γ₅.
    use eq_in_prod_partial_setoid.
    + cbn.
      hypersimplify.
      fold γ₂.
      use (partial_setoid_mor_unique_im s).
      * exact γ₁.
      * use weaken_left.
        do 2 use weaken_right.
        apply hyperdoctrine_hyp.
      * use (partial_setoid_mor_eq_defined s).
        ** exact γ₅.
        ** exact γ₃.
        ** use weaken_left.
           use weaken_right.
           do 2 use weaken_left.
           apply hyperdoctrine_hyp.
        ** do 2 use weaken_left.
           use weaken_right.
           use weaken_left.
           exact (partial_setoid_mor_cod_defined s _ _ (hyperdoctrine_hyp _)).
        ** do 2 use weaken_left.
           use weaken_right.
           use weaken_left.
           apply hyperdoctrine_hyp.
    + cbn.
      hypersimplify.
      fold a₂.
      refine (partial_setoid_trans _ _ _).
      {
        do 2 use weaken_right.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      use weaken_left.
      use weaken_right.
      use partial_setoid_sym.
      apply hyperdoctrine_hyp.
Qed.
