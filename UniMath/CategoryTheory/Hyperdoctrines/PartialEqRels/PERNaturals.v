(**

 Natural numbers in the tripos to topos construction

 We construct a natural numbers object in toposes associated to a (weak) tripos. To
 do so, we assume that the tripos comes with a type `N` together with terms representing
 zero and successor, such that zero isn't the successor of any inhabitant of `N` and
 such that taking the successor is an injective map. We construct the natural numbers
 object in `N` by restricting `N` to the inductively generated natural numbers. Note
 that this construction essentially uses impredicativity, since we define the inductively
 generated natural numbers by taking the intersection of all subsets that contain `0`
 and that are closed under taking the successor.

 In this file, we show the necessary statements to conclude that we get a natural numbers
 object. Most of the work lies in constructing the partial setoid morphism arising from
 the universal property and in establishing uniqueness. The universal morphism is defined
 as a functional relation, which requires, among others, establishing well-definedness and
 that every point in the domain has an image. Both proofs require induction. The other
 required properties of this partial setoid morphism can be established rather directly.
 Uniqueness also is established using induction.

 Content
 1. The zero partial setoid morphism
 2. The successor partial setoid morphism
 3. The recursion principle
 4. The β-rules
 5. Uniqueness
 6. The natural numbers object

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HyperdoctrineNat.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERTerminal.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.InductivePER.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.NNORecursiveMap.

Local Open Scope cat.
Local Open Scope hd.
Local Open Scope weak_tripos.

Section PERNats.
  Context {H : weak_tripos}
          (N : first_order_hyperdoctrine_nats H).

  (** * 1. The zero partial setoid morphism *)
  Definition nat_per_Z_form
    : form (eq_partial_setoid 𝟙 ×h nat_partial_setoid N)
    := π₂ (tm_var _) ≡ hd_nats_z N _.

  Arguments nat_per_Z_form /.

  Proposition nat_per_Z_laws
    : partial_setoid_morphism_laws nat_per_Z_form.
  Proof.
    repeat split.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite subst_hd_nats_z.
      use eq_in_eq_partial_setoid.
      apply hyperdoctrine_unit_tm_eq.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite subst_hd_nats_z.
     pose (n := π₂ (tm_var ((𝟙 ×h 𝟙) ×h N))).
      fold n.
      use eq_in_nat_partial_setoid.
      + apply hyperdoctrine_refl.
      + refine (hyperdoctrine_eq_transportb _ _ _).
        * apply hyperdoctrine_hyp.
        * apply is_inductive_zero.
    - do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_z.
      pose (Γ := (((𝟙 ×h 𝟙) ×h 𝟙) ×h N) ×h N).
      fold Γ.
      pose (n := π₂ (π₁ (tm_var Γ))).
      pose (m := π₂ (tm_var Γ)).
      pose (z₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      pose (z₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
      fold n m z₁ z₂.
      refine (hyperdoctrine_eq_trans _ _).
      {
        use weaken_left.
        use weaken_right.
        use hyperdoctrine_eq_sym.
        use eq_nat_partial_setoid_to_eq.
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      apply hyperdoctrine_hyp.
    - do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_z.
      pose (Γ := ((𝟙 ×h 𝟙) ×h N) ×h N).
      fold Γ.
      pose (n := π₂ (π₁ (tm_var Γ))).
      pose (m := π₂ (tm_var Γ)).
      fold n m.
      use eq_in_nat_partial_setoid.
      + refine (hyperdoctrine_eq_trans _ _).
        {
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        use weaken_right.
        use hyperdoctrine_eq_sym.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        refine (hyperdoctrine_eq_transportb _ _ _).
        * apply hyperdoctrine_hyp.
        * apply is_inductive_zero.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_z.
      use exists_intro.
      {
        exact (hd_nats_z _ _).
      }
      hypersimplify.
      rewrite subst_hd_nats_z.
      hypersimplify.
      apply hyperdoctrine_refl.
  Qed.

  Definition nat_per_Z
    : partial_setoid_morphism
        (eq_partial_setoid 𝟙)
        (nat_partial_setoid N).
  Proof.
    use make_partial_setoid_morphism.
    - exact nat_per_Z_form.
    - exact nat_per_Z_laws.
  Defined.

  (** * 2. The successor partial setoid morphism *)
  Definition nat_per_S_form
    : form (nat_partial_setoid N ×h nat_partial_setoid N)
    := let n := π₁ (tm_var (nat_partial_setoid N ×h N)) in
       let m := π₂ (tm_var (N ×h N)) in
       (n ~ n) ∧ hd_nats_s N n ≡ m.

  Arguments nat_per_S_form /.

  Proposition nat_per_S_laws
    : partial_setoid_morphism_laws nat_per_S_form.
  Proof.
    repeat split.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite subst_hd_nats_s.
      hypersimplify.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      pose (n := π₂ (π₁ (tm_var ((𝟙 ×h N) ×h N)))).
      pose (m := π₂ (tm_var ((𝟙 ×h N) ×h N))).
      fold n m.
      use weaken_left.
      apply hyperdoctrine_hyp.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite subst_hd_nats_s.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      pose (n := π₂ (π₁ (tm_var ((𝟙 ×h N) ×h N)))).
      pose (m := π₂ (tm_var ((𝟙 ×h N) ×h N))).
      fold n m.
      use eq_in_nat_partial_setoid.
      + apply hyperdoctrine_refl.
      + refine (hyperdoctrine_eq_transportf _ _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        use is_inductive_suc.
        refine (eq_nat_partial_setoid_to_inductive _ _).
        apply hyperdoctrine_hyp.
    - do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      pose (Γ := (((𝟙 ×h N) ×h N) ×h N) ×h N).
      fold Γ.
      pose (n₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      pose (n₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (m₁ := π₂ (π₁ (tm_var Γ))).
      pose (m₂ := π₂ (tm_var Γ)).
      fold n₁ n₂ m₁ m₂.
      use conj_intro.
      + do 2 use weaken_left.
        refine (partial_setoid_refl_r _).
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_eq_trans _ _).
        {
          refine (app_hd_nat_s _ _).
          use hyperdoctrine_eq_sym.
          do 2 use weaken_left.
          apply eq_nat_partial_setoid_to_eq.
          apply hyperdoctrine_hyp.
        }
        refine (hyperdoctrine_eq_trans _ _).
        {
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        use weaken_right.
        apply eq_nat_partial_setoid_to_eq.
        apply hyperdoctrine_hyp.
    - do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      pose (Γ := ((𝟙 ×h N) ×h N) ×h N).
      fold Γ.
      pose (n := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (m₁ := π₂ (π₁ (tm_var Γ))).
      pose (m₂ := π₂ (tm_var Γ)).
      fold m₁ m₂ n.
      use eq_in_nat_partial_setoid.
      + refine (hyperdoctrine_eq_trans _ _).
        {
          use weaken_left.
          use weaken_right.
          use hyperdoctrine_eq_sym.
          apply hyperdoctrine_hyp.
        }
        do 2 use weaken_right.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_eq_transportf _ _ _).
        {
          use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use is_inductive_suc.
        do 2 use weaken_left.
        refine (eq_nat_partial_setoid_to_inductive _ _).
        apply hyperdoctrine_hyp.
    - use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      pose (n := π₂ (tm_var (𝟙 ×h N))).
      use exists_intro.
      {
        exact (hd_nats_s _ n).
      }
      hypersimplify.
      rewrite subst_hd_nats_s.
      rewrite !hyperdoctrine_pr2_subst.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      cbn.
      fold n.
      use conj_intro.
      + apply hyperdoctrine_hyp.
      + apply hyperdoctrine_refl.
  Qed.

  Definition nat_per_S
    : partial_setoid_morphism
        (nat_partial_setoid N)
        (nat_partial_setoid N).
  Proof.
    use make_partial_setoid_morphism.
    - exact nat_per_S_form.
    - exact nat_per_S_laws.
  Defined.

  (** * 3. The recursion principle *)
  Section Mapping.
    Context {X : partial_setoid H}
            (zX : partial_setoid_morphism (eq_partial_setoid 𝟙) X)
            (sX : partial_setoid_morphism X X).

    Let φ : form (nat_partial_setoid N ×h X)
      := nat_per_rec_form N zX sX.

    Proposition nat_per_rec_dom_defined
      : partial_setoid_mor_dom_defined_law φ.
    Proof.
      unfold φ.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      pose (Γ := (𝟙 ×h N) ×h X).
      fold Γ.
      pose (n := π₂ (π₁ (tm_var Γ))).
      pose (x := π₂ (tm_var Γ)).
      fold n x.
      unfold nat_per_rec_form.
      hypersimplify.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition nat_per_rec_cod_defined
      : partial_setoid_mor_cod_defined_law φ.
    Proof.
      unfold φ.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      pose (Γ := (𝟙 ×h N) ×h X).
      fold Γ.
      pose (n := π₂ (π₁ (tm_var Γ))).
      pose (x := π₂ (tm_var Γ)).
      fold n x.
      unfold nat_per_rec_form.
      hypersimplify.
      use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition nat_per_rec_eq_defined
      : partial_setoid_mor_eq_defined_law φ.
    Proof.
      unfold φ.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      cbn.
      unfold nat_per_rec_form.
      hypersimplify.
      repeat use conj_intro.
      - do 2 use weaken_left.
        refine (partial_setoid_refl_r _).
        apply hyperdoctrine_hyp.
      - use weaken_left.
        use weaken_right.
        refine (partial_setoid_refl_r _).
        apply hyperdoctrine_hyp.
      - do 2 use hyp_rtrans.
        use hyp_sym.
        unfold nat_per_rec_form_def.
        hypersimplify.
        use forall_intro.
        do 2 use impl_intro.
        hypersimplify.
        pose (Γ := ((((𝟙 ×h N) ×h N) ×h X) ×h X) ×h ℙ (N ×h X)).
        fold Γ.
        pose (p := π₂ (tm_var Γ)).
        pose (x₂ := π₂ (π₁ (tm_var Γ))).
        pose (x₁ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (n₂ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (n₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        cbn.
        fold x₁ x₂ n₁ n₂ p.
        do 2 use hyp_ltrans.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact p.
        }
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        use impl_intro.
        fold n₁ x₁ p.
        refine (exp_partial_setoid_extensional (nat_partial_setoid N) _ _ _ _ _).
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + do 6 use weaken_left.
          apply hyperdoctrine_hyp.
        + do 5 use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + refine (impl_elim _ _).
          {
            use weaken_right.
            apply hyperdoctrine_hyp.
          }
          refine (impl_elim _ _).
          {
            do 2 use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
          }
          refine (impl_elim _ _).
          {
            do 2 use weaken_left.
            use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          }
          use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.

    Definition nat_per_rec_eq_unique_im_ind_form
               (Γ : ty H)
      : form (((N ×h Γ) ×h X) ×h X)
      := let y := π₂ (tm_var _) in
         let x := π₂ (π₁ (tm_var _)) in
         let n := π₁ (π₁ (π₁ (tm_var _))) in
         (nat_per_rec_form N zX sX) [ ⟨ n , x ⟩ ]
         ⇒ (nat_per_rec_form N zX sX) [ ⟨ n , y ⟩ ]
         ⇒ x ~ y.

    Proposition nat_per_rec_eq_unique_im_ind
                {Γ : ty H}
                {Δ : form Γ}
                (n : tm Γ (nat_partial_setoid N))
                (p : Δ ⊢ n ~ n)
      : Δ ⊢ (∀h ∀h (nat_per_rec_eq_unique_im_ind_form Γ)) [ ⟨ n , tm_var _ ⟩ ].
    Proof.
      use is_inductive_nat_induction.
      - hypersimplify.
        do 2 use forall_intro.
        unfold nat_per_rec_eq_unique_im_ind_form.
        hypersimplify.
        rewrite subst_hd_nats_z.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        pose (Γ' := (Γ ×h X) ×h X).
        fold Γ'.
        pose (y := π₂ (tm_var Γ')).
        pose (x := π₂ (π₁ (tm_var Γ'))).
        fold x y.
        refine (hyperdoctrine_cut _ _).
        {
          refine (conj_intro _ _).
          {
            use weaken_left.
            refine (hyperdoctrine_proof_subst _ _).
            apply to_nat_per_rec_spec.
          }
          use weaken_right.
          refine (hyperdoctrine_proof_subst _ _).
          apply to_nat_per_rec_spec.
        }
        unfold nat_per_rec_spec.
        cbn.
        hypersimplify.
        rewrite !subst_hd_nats_z.
        refine (disj_elim _ _ _).
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + use hyp_ltrans.
          use weaken_right.
          refine (disj_elim _ _ _).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use hyp_ltrans.
            use weaken_right.
            use (partial_setoid_mor_unique_im zX _ _).
            ** exact !!.
            ** use weaken_left.
               use weaken_right.
               apply hyperdoctrine_hyp.
            ** do 2 use weaken_right.
               apply hyperdoctrine_hyp.
          * use hyp_ltrans.
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
            use hyp_sym.
            refine (exists_elim _ _).
            {
              use weaken_left.
              apply hyperdoctrine_hyp.
            }
            rewrite conj_subst.
            use hyp_ltrans.
            use weaken_right.
            unfold nat_per_rec_spec_suc.
            hypersimplify.
            refine (first_order_hyperdoctrine_nats_z_neq_s_all N _ _).
            refine (hyperdoctrine_eq_trans _ _).
            ** use weaken_right.
               use weaken_left.
               use hyperdoctrine_eq_sym.
               rewrite subst_hd_nats_s.
               apply hyperdoctrine_hyp.
            ** do 2 use weaken_left.
               rewrite subst_hd_nats_z.
               apply hyperdoctrine_hyp.
        + use hyp_ltrans.
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
          refine (disj_elim _ _ _).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use hyp_ltrans.
            use weaken_right.
            unfold nat_per_rec_spec_suc.
            hypersimplify.
            refine (first_order_hyperdoctrine_nats_z_neq_s_all N _ _).
            refine (hyperdoctrine_eq_trans _ _).
            ** do 2 use weaken_left.
               rewrite subst_hd_nats_s.
               use hyperdoctrine_eq_sym.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               rewrite subst_hd_nats_z.
               apply hyperdoctrine_hyp.
          * use hyp_ltrans.
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
            unfold nat_per_rec_spec_suc.
            unfold Γ', x, y.
            hypersimplify.
            clear Γ' x y.
            do 2 use weaken_left.
            rewrite subst_hd_nats_z.
            rewrite subst_hd_nats_s.
            refine (first_order_hyperdoctrine_nats_z_neq_s_all N _ _).
            use hyperdoctrine_eq_sym.
            apply hyperdoctrine_hyp.
      - hypersimplify.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use forall_intro.
        hypersimplify.
        match goal with
        | |- ?H ⊢ _ => pose (IH := H) ; fold IH
        end.
        unfold nat_per_rec_eq_unique_im_ind_form.
        hypersimplify.
        do 2 use impl_intro.
        pose (Γ' := ((Γ ×h N) ×h X) ×h X).
        pose (y := π₂ (tm_var Γ')).
        pose (x := π₂ (π₁ (tm_var Γ'))).
        pose (m := π₂ (π₁ (π₁ (tm_var Γ')))).
        fold Γ' x y m.
        use hyp_ltrans.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !var_tm_subst.
        fold m.
        refine (hyperdoctrine_cut _ _).
        {
          refine (conj_intro (weaken_left (hyperdoctrine_hyp _) _) _).
          use weaken_right.
          refine (conj_intro _ _).
          + use weaken_left.
            refine (hyperdoctrine_proof_subst _ _).
            apply to_nat_per_rec_spec.
          + use weaken_right.
            refine (hyperdoctrine_proof_subst _ _).
            apply to_nat_per_rec_spec.
        }
        use hyp_sym.
        use hyp_ltrans.
        refine (disj_elim _ _ _).
        + use weaken_left.
          unfold nat_per_rec_spec.
          hypersimplify.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          use weaken_left.
          rewrite subst_hd_nats_z.
          refine (first_order_hyperdoctrine_nats_z_neq_s_all N _ _).
          apply hyperdoctrine_hyp.
        + use hyp_ltrans.
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
          refine (disj_elim _ _ _).
          * use weaken_left.
            unfold nat_per_rec_spec.
            hypersimplify.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use weaken_left.
            rewrite subst_hd_nats_z, subst_hd_nats_s.
            refine (first_order_hyperdoctrine_nats_z_neq_s_all N _ _).
            apply hyperdoctrine_hyp.
          * use hyp_ltrans.
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
            unfold x, y, m, Γ'.
            clear Γ' x y m.
            pose (Γ' := ((((((Γ ×h N) ×h X) ×h X) ×h N) ×h X) ×h N) ×h X).
            fold Γ'.
            pose (y := π₂ (tm_var Γ')).
            pose (m₁ := π₂ (π₁ (tm_var Γ'))).
            pose (x := π₂ (π₁ (π₁ (tm_var Γ')))).
            pose (m₂ := π₂ (π₁ (π₁ (π₁ (tm_var Γ'))))).
            pose (sy := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))).
            pose (sx := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ'))))))).
            pose (m₃ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))))).
            pose (γ := π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ')))))))).
            rewrite subst_hd_nats_s.
            rewrite !hyperdoctrine_pr2_subst.
            rewrite !hyperdoctrine_pr1_subst.
            rewrite !var_tm_subst.
            fold x m₁ y m₂ sx sy m₃.
            unfold nat_per_rec_spec_suc.
            hypersimplify.
            rewrite !subst_hd_nats_s.
            rewrite !hyperdoctrine_pr2_subst.
            rewrite !hyperdoctrine_pr1_subst.
            rewrite !var_tm_subst.
            rewrite !hyperdoctrine_pair_pr1.
            rewrite !hyperdoctrine_pair_pr2.
            refine (weaken_cut _ _).
            {
              use weaken_left.
              unfold IH.
              rewrite forall_subst.
              refine (forall_elim (hyperdoctrine_hyp _) _).
              exact x.
            }
            use hyp_ltrans.
            use weaken_right.
            hypersimplify.
            use hyp_sym.
            refine (weaken_cut _ _).
            {
              use weaken_left.
              refine (forall_elim (hyperdoctrine_hyp _) _).
              exact y.
            }
            use hyp_ltrans.
            use weaken_right.
            hypersimplify.
            fold m₃ γ.
            unfold nat_per_rec_eq_unique_im_ind_form.
            hypersimplify.
            refine (partial_setoid_mor_unique_im sX _ _).
            {
              do 2 use weaken_left.
              use weaken_right.
              use weaken_left.
              apply hyperdoctrine_hyp.
            }
            refine (partial_setoid_mor_eq_defined sX _ _ _).
            ** use partial_setoid_sym.
               refine (impl_elim _ (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _))).
               *** use weaken_left.
                   use weaken_right.
                   use hyp_sym.
                   use hyp_ltrans.
                   use weaken_right.
                   refine (hyperdoctrine_eq_transportb
                             _
                             _
                             (weaken_left (hyperdoctrine_hyp _) _)).
                   use weaken_right.
                   use hyperdoctrine_eq_prod_eq.
                   **** hypersimplify.
                        use first_order_hyperdoctrine_nats_s_mono.
                        apply hyperdoctrine_hyp.
                   **** hypersimplify.
                        apply hyperdoctrine_refl.
               *** do 2 use weaken_left.
                   use hyp_sym.
                   use hyp_ltrans.
                   use weaken_right.
                   refine (hyperdoctrine_eq_transportb
                             _
                             _
                             (weaken_left (hyperdoctrine_hyp _) _)).
                   use weaken_right.
                   use hyperdoctrine_eq_prod_eq.
                   **** hypersimplify.
                        use first_order_hyperdoctrine_nats_s_mono.
                        apply hyperdoctrine_hyp.
                   **** hypersimplify.
                        apply hyperdoctrine_refl.
            ** use weaken_left.
               do 2 use weaken_right.
               use weaken_left.
               refine (partial_setoid_mor_cod_defined _ _ _ _).
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               do 2 use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
      - refine (hyperdoctrine_cut p _).
        refine (eq_nat_partial_setoid_to_inductive _ _).
        apply hyperdoctrine_hyp.
    Qed.

    Proposition nat_per_rec_eq_unique_im
      : partial_setoid_mor_unique_im_law φ.
    Proof.
      unfold φ.
      do 3 use forall_intro.
      cbn.
      use impl_intro.
      use weaken_right.
      refine (weaken_cut _ _).
      {
        refine (hyperdoctrine_cut (truth_intro _) _).
        refine (hyperdoctrine_cut _ (hyperdoctrine_proof_subst !! nat_per_rec_dom_defined)).
        rewrite truth_subst.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      use hyp_sym.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (π₁ (π₁ (tm_var _)))).
      }
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      use hyp_sym.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (π₁ (tm_var _))).
      }
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      use hyp_sym.
      refine (weaken_cut _ _).
      {
        refine (impl_elim _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      use hyp_ltrans.
      use weaken_right.
      refine (impl_elim _ _).
      {
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      refine (hyperdoctrine_cut _ _).
      {
        exact (nat_per_rec_eq_unique_im_ind _ (hyperdoctrine_hyp _)).
      }
      hypersimplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (π₁ (tm_var _))).
      }
      hypersimplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (tm_var _)).
      }
      unfold nat_per_rec_eq_unique_im_ind_form.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Definition nat_per_rec_hom_exists_form
                (Γ : ty H)
      : form (nat_partial_setoid N ×h Γ)
      := (∃h ((nat_per_rec_form N zX sX) [ ⟨ π₁ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩ ])).

    Proposition nat_per_rec_hom_exists_ind
                {Γ : ty H}
                {Δ : form Γ}
                (n : tm Γ (nat_partial_setoid N))
                (p : Δ ⊢ n ~ n)
      : Δ ⊢ (nat_per_rec_hom_exists_form Γ) [ ⟨ n , tm_var _ ⟩ ].
    Proof.
      use is_inductive_nat_induction.
      - unfold nat_per_rec_hom_exists_form.
        hypersimplify.
        refine (exists_elim _ _).
        {
          use (partial_setoid_mor_hom_exists zX).
          {
            exact !!.
          }
          use eq_in_eq_partial_setoid.
          apply hyperdoctrine_refl.
        }
        use weaken_right.
        hypersimplify.
        use exists_intro.
        {
          exact (π₂ (tm_var (Γ ×h X))).
        }
        unfold nat_per_rec_form.
        hypersimplify.
        rewrite subst_hd_nats_z.
        repeat use conj_intro.
        + use nat_partial_setoid_refl.
          apply is_inductive_zero.
        + refine (partial_setoid_mor_cod_defined zX _ _ _).
          apply hyperdoctrine_hyp.
        + unfold nat_per_rec_form_def.
          hypersimplify.
          use forall_intro.
          hypersimplify.
          rewrite subst_hd_nats_z.
          pose (f := π₂ (tm_var ((Γ ×h X) ×h ℙ (N ×h X)))).
          pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h ℙ (N ×h X))))).
          pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h ℙ (N ×h X))))).
          fold γ x f.
          use impl_intro.
          do 2 (use impl_intro ; use weaken_left).
          unfold map_contains_z.
          hypersimplify.
          use hyp_sym.
          refine (weaken_cut _ _).
          {
            use weaken_left.
            refine (forall_elim (hyperdoctrine_hyp _) _).
            exact x.
          }
          use hyp_ltrans.
          use weaken_right.
          hypersimplify.
          refine (impl_elim _ _).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            rewrite subst_hd_nats_z.
            apply hyperdoctrine_hyp.
      - refine (hyperdoctrine_cut p _).
        use forall_intro.
        use impl_intro.
        use hyp_sym.
        unfold nat_per_rec_hom_exists_form.
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
        refine (exists_elim _ _).
        {
          refine (partial_setoid_mor_hom_exists sX _).
          refine (weaken_cut _ _).
          {
            refine (hyperdoctrine_cut
                      _
                      (hyperdoctrine_proof_subst !! (nat_per_rec_cod_defined))).
            hypersimplify.
            apply truth_intro.
          }
          use hyp_sym.
          hypersimplify.
          refine (weaken_cut _ _).
          {
            use weaken_left.
            refine (forall_elim (hyperdoctrine_hyp _) _).
            exact (π₂ (π₁ (tm_var _))).
          }
          use hyp_ltrans.
          use weaken_right.
          hypersimplify.
          use hyp_sym.
          refine (weaken_cut _ _).
          {
            use weaken_left.
            refine (forall_elim (hyperdoctrine_hyp _) _).
            exact (π₂ (tm_var _)).
          }
          use hyp_ltrans.
          use weaken_right.
          hypersimplify.
          refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
          use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        use exists_intro.
        {
          exact (π₂ (tm_var _)).
        }
        hypersimplify.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !var_tm_subst.
        use hyp_ltrans.
        use weaken_right.
        refine (hyperdoctrine_cut
                  _
                  (hyperdoctrine_proof_subst
                     _
                     (from_nat_per_rec_spec N zX sX))).
        unfold nat_per_rec_spec.
        hypersimplify.
        use disj_intro_right.
        hypersimplify.
        clear n p.
        pose (y := π₂ (tm_var (((Γ ×h N) ×h X) ×h X))).
        pose (x := π₂ (π₁ (tm_var (((Γ ×h N) ×h X) ×h X)))).
        pose (n := π₂ (π₁ (π₁ (tm_var (((Γ ×h N) ×h X) ×h X))))).
        fold n x y.
        use exists_intro.
        {
          exact n.
        }
        hypersimplify.
        use exists_intro.
        {
          exact x.
        }
        cbn.
        hypersimplify.
        fold y.
        unfold nat_per_rec_spec_suc.
        hypersimplify.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !hyperdoctrine_pr1_subst.
        rewrite !var_tm_subst.
        rewrite !hyperdoctrine_pair_pr1.
        rewrite !hyperdoctrine_pair_pr2.
        repeat use conj_intro.
        + apply hyperdoctrine_refl.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
      - refine (eq_nat_partial_setoid_to_inductive _ _).
        exact p.
    Qed.

    Proposition nat_per_rec_hom_exists
      : partial_setoid_mor_hom_exists_law φ.
    Proof.
      unfold φ.
      use forall_intro.
      use impl_intro.
      refine (hyperdoctrine_cut _ _).
      {
        use (nat_per_rec_hom_exists_ind (π₂ (tm_var _))).
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      unfold nat_per_rec_hom_exists_form.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition nat_per_rec_laws
      : partial_setoid_morphism_laws φ.
    Proof.
      repeat split.
      - exact nat_per_rec_dom_defined.
      - exact nat_per_rec_cod_defined.
      - exact nat_per_rec_eq_defined.
      - exact nat_per_rec_eq_unique_im.
      - exact nat_per_rec_hom_exists.
    Defined.

    Definition nat_per_rec
      : partial_setoid_morphism (nat_partial_setoid N) X.
    Proof.
      use make_partial_setoid_morphism.
      - exact (nat_per_rec_form N zX sX).
      - exact nat_per_rec_laws.
    Defined.

    (** * 4. The β-rules *)
    Proposition nat_per_rec_Z
      : partial_setoid_comp_morphism nat_per_Z nat_per_rec = zX.
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        refine (exists_elim _ _).
        {
          apply hyperdoctrine_hyp.
        }
        use weaken_right.
        hypersimplify.
        rewrite subst_hd_nats_z.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var _))).
        hypersimplify.
        rewrite (hyperdoctrine_unit_eta (π₁ (π₁ (tm_var _)))).
        use (nat_per_rec_form_z_inv N zX sX).
        hypersimplify.
        refine (hyperdoctrine_eq_transportb
                  _
                  _
                  (weaken_right (hyperdoctrine_hyp _) _)).
        use weaken_left.
        use hyperdoctrine_eq_prod_eq.
        + hypersimplify.
          use hyperdoctrine_eq_sym.
          apply hyperdoctrine_hyp.
        + hypersimplify.
          apply hyperdoctrine_refl.
      - rewrite <- (hyperdoctrine_id_subst zX).
        rewrite (hyperdoctrine_pair_eta (tm_var _)).
        rewrite (hyperdoctrine_unit_eta (π₁ (tm_var (eq_partial_setoid 𝟙 ×h X)))).
        refine (hyperdoctrine_cut _ _).
        {
          refine (nat_per_rec_form_z N zX sX _).
          apply hyperdoctrine_hyp.
        }
        cbn.
        use exists_intro.
        {
          exact (hd_nats_z N _).
        }
        hypersimplify.
        rewrite subst_hd_nats_z.
        use conj_intro.
        + apply hyperdoctrine_refl.
        + apply hyperdoctrine_hyp.
    Qed.

    Proposition nat_per_rec_S
      : partial_setoid_comp_morphism nat_per_S nat_per_rec
        =
        partial_setoid_comp_morphism nat_per_rec sX.
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        refine (exists_elim (hyperdoctrine_hyp _) _).
        use weaken_right.
        hypersimplify.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr1_subst.
        rewrite !var_tm_subst.
        rewrite !hyperdoctrine_pair_pr1.
        pose (n := π₁ (π₁ (tm_var ((N ×h X) ×h N)))).
        pose (x := π₂ (π₁ (tm_var ((N ×h X) ×h N)))).
        pose (sn := π₂ (tm_var ((N ×h X) ×h N))).
        fold n sn x.
        refine (hyperdoctrine_cut _ _).
        {
          simple refine (nat_per_rec_form_s_inv N zX sX _).
          + exact n.
          + exact x.
          + refine (hyperdoctrine_eq_transportb
                      _
                      _
                      (weaken_right (hyperdoctrine_hyp _) _)).
            use weaken_left.
            use hyperdoctrine_eq_prod_eq.
            * hypersimplify.
              use weaken_right.
              apply hyperdoctrine_hyp.
            * hypersimplify.
              apply hyperdoctrine_refl.
        }
        refine (exists_elim (hyperdoctrine_hyp _) _).
        use weaken_right.
        hypersimplify.
        use exists_intro.
        {
          exact (π₂ (tm_var _)).
        }
        unfold n, x.
        hypersimplify.
        use conj_intro.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
      - cbn.
        refine (exists_elim (hyperdoctrine_hyp _) _).
        use weaken_right.
        hypersimplify.
        pose (n := π₁ (π₁ (tm_var ((N ×h X) ×h X)))).
        pose (sx := π₂ (π₁ (tm_var ((N ×h X) ×h X)))).
        pose (x := π₂ (tm_var ((N ×h X) ×h X))).
        fold n x sx.
        use exists_intro.
        {
          exact (hd_nats_s N n).
        }
        hypersimplify.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr1_subst.
        rewrite !var_tm_subst.
        rewrite !hyperdoctrine_pair_pr1.
        cbn.
        fold n x sx.
        repeat use conj_intro.
        + use weaken_left.
          refine (partial_setoid_mor_dom_defined nat_per_rec _ _ _).
          apply hyperdoctrine_hyp.
        + apply hyperdoctrine_refl.
        + use nat_per_rec_form_s.
          * exact x.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
    Qed.

    (** * 5. Uniqueness *)
    Proposition nat_per_rec_unique
                (ψ : partial_setoid_morphism (nat_partial_setoid N) X)
                (p₁ : partial_setoid_comp_morphism nat_per_Z ψ = zX)
                (p₂ : partial_setoid_comp_morphism nat_per_S ψ
                      =
                      partial_setoid_comp_morphism ψ sX)
      : ψ = nat_per_rec.
    Proof.
      use eq_partial_setoid_morphism.
      - use eq_nat_partial_setoid_morphism.
        + clear p₂.
          unfold partial_setoid_mor_contains_Z.
          use impl_intro.
          use weaken_right.
          use nat_per_rec_form_z.
          use (from_eq_partial_setoid_morphism_f p₁).
          cbn.
          hypersimplify.
          use exists_intro.
          {
            exact (hd_nats_z N _).
          }
          hypersimplify.
          rewrite subst_hd_nats_z.
          use conj_intro.
          * apply hyperdoctrine_refl.
          * apply hyperdoctrine_hyp.
        + clear p₁.
          unfold partial_setoid_mor_contains_S.
          use impl_intro.
          use weaken_right.
          refine (exists_elim _ _).
          {
            apply hyperdoctrine_hyp.
          }
          use weaken_right.
          hypersimplify.
          use impl_intro.
          refine (weaken_cut _ _).
          {
            simple refine (from_eq_partial_setoid_morphism_f p₂ _).
            * exact (π₁ (π₁ (tm_var _))).
            * exact (π₂ (π₁ (tm_var _))).
            * cbn.
              hypersimplify.
              use exists_intro.
              {
                exact (hd_nats_s N (π₁ (π₁ (tm_var _)))).
              }
              hypersimplify.
              rewrite !subst_hd_nats_s.
              rewrite !hyperdoctrine_pr1_subst.
              rewrite !var_tm_subst.
              rewrite !hyperdoctrine_pair_pr1.
              repeat use conj_intro.
              ** do 2 use weaken_left.
                 refine (partial_setoid_mor_dom_defined ψ _ _ _).
                 apply hyperdoctrine_hyp.
              ** apply hyperdoctrine_refl.
              ** use weaken_right.
                 apply hyperdoctrine_hyp.
          }
          use hyp_sym.
          cbn.
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
          cbn.
          rewrite subst_hd_nats_s.
          rewrite !hyperdoctrine_pr1_subst.
          rewrite !var_tm_subst.
          use nat_per_rec_form_s.
          * exact (π₂ (tm_var _)).
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
          * refine (partial_setoid_mor_eq_defined nat_per_rec _ _ _).
            ** do 2 use weaken_left.
               use weaken_right.
               refine (partial_setoid_mor_dom_defined nat_per_rec _ _ _).
               apply hyperdoctrine_hyp.
            ** refine (partial_setoid_mor_unique_im ψ _ _).
               *** do 3 use weaken_left.
                   apply hyperdoctrine_hyp.
               *** use weaken_right.
                   use weaken_left.
                   apply hyperdoctrine_hyp.
            ** do 2 use weaken_left.
               use weaken_right.
               apply hyperdoctrine_hyp.
      - use eq_nat_partial_setoid_morphism.
        + clear p₂.
          unfold partial_setoid_mor_contains_Z.
          use impl_intro.
          use weaken_right.
          refine (hyperdoctrine_cut _ _).
          {
            refine (from_eq_partial_setoid_morphism_b p₁ _).
            apply (nat_per_rec_form_z_inv N zX sX).
            apply hyperdoctrine_hyp.
          }
          cbn.
          hypersimplify.
          refine (exists_elim _ _).
          {
            apply hyperdoctrine_hyp.
          }
          use weaken_right.
          hypersimplify.
          cbn.
          rewrite !subst_hd_nats_z.
          refine (hyperdoctrine_eq_transportb
                    _
                    _
                    (weaken_right (hyperdoctrine_hyp _) _)).
          use hyperdoctrine_eq_prod_eq.
          * hypersimplify.
            use hyperdoctrine_eq_sym.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * hypersimplify.
            apply hyperdoctrine_refl.
        + clear p₁.
          unfold partial_setoid_mor_contains_S.
          use impl_intro.
          use weaken_right.
          refine (exists_elim _ _).
          {
            apply hyperdoctrine_hyp.
          }
          use weaken_right.
          hypersimplify.
          cbn.
          rewrite subst_hd_nats_s.
          rewrite !hyperdoctrine_pr1_subst.
          rewrite !var_tm_subst.
          use impl_intro.
          refine (weaken_cut _ _).
          {
            use weaken_right.
            apply nat_per_rec_form_s_inv.
            apply hyperdoctrine_hyp.
          }
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
          refine (weaken_cut _ _).
          {
            simple refine (from_eq_partial_setoid_morphism_b p₂ _).
            + exact (π₁ (π₁ (π₁ (tm_var _)))).
            + exact (π₂ (π₁ (π₁ (tm_var _)))).
            + cbn.
              hypersimplify.
              use exists_intro.
              {
                exact (π₂ (tm_var _)).
              }
              hypersimplify.
              rewrite !subst_hd_nats_s.
              rewrite !hyperdoctrine_pr1_subst.
              rewrite !var_tm_subst.
              use conj_intro.
              * refine (partial_setoid_mor_eq_defined ψ _ _ _).
                ** do 2 use weaken_left.
                   use weaken_right.
                   refine (partial_setoid_mor_dom_defined ψ _ _ _).
                   apply hyperdoctrine_hyp.
                ** refine (partial_setoid_mor_unique_im nat_per_rec _ _).
                   *** do 3 use weaken_left.
                       apply hyperdoctrine_hyp.
                   *** do 2 use weaken_right.
                       apply hyperdoctrine_hyp.
                ** do 2 use weaken_left.
                   use weaken_right.
                   apply hyperdoctrine_hyp.
              * use weaken_right.
                use weaken_left.
                apply hyperdoctrine_hyp.
          }
          cbn.
          use hyp_sym.
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
          rewrite !subst_hd_nats_s.
          rewrite !hyperdoctrine_pr1_subst.
          rewrite !var_tm_subst.
          rewrite !hyperdoctrine_pair_pr1.
          use weaken_right.
          use hyp_ltrans.
          use weaken_right.
          refine (hyperdoctrine_eq_transportf
                    _
                    _
                    (weaken_right (hyperdoctrine_hyp _) _)).
          use weaken_left.
          use hyperdoctrine_eq_prod_eq.
          * hypersimplify.
            use hyperdoctrine_eq_sym.
            apply hyperdoctrine_hyp.
          * hypersimplify.
            apply hyperdoctrine_refl.
    Qed.
  End Mapping.

  (** * 6. The natural numbers object *)
  Definition category_of_partial_setoids_NNO
    : NNO (terminal_partial_setoid H).
  Proof.
    use make_NNO.
    - exact (nat_partial_setoid N).
    - exact nat_per_Z.
    - exact nat_per_S.
    - intros X zX sX.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (nat_per_rec zX sX).
        * exact (nat_per_rec_Z zX sX).
        * exact (nat_per_rec_S zX sX).
      + abstract
          (intros ψ ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           cbn ;
           exact (nat_per_rec_unique zX sX (pr1 ψ) (pr12 ψ) (pr22 ψ))).
  Defined.
End PERNats.
