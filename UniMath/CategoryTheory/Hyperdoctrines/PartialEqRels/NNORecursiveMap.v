(**

 Recursive maps from the natural numbers

 We show how to construct recursive maps from the natural numbers to other partial
 setoids that are equipped with a zero and a successor map.

 The map is represented by a formula, and the first main point is that we give an
 impredicative definition of this formula. Specifically, we take the intersection of
 some collection of relations between `N` and `X`. We look at those relations that
 satisfy the recursive equations of the map, and that respect equality. In another
 file we show that this intersection gives rise to a functional relation and thus to
 a morphism in the category of partial setoids.  We show that the resulting formula
 satisfies the expected recursive equation ([nat_per_rec_spec_iff]), which simplifies
 proving properties of this map.

 We also prove the computation rules for zero and the successor. The most interesting
 part here is that here we use axioms for natural numbers in the tripos. For the
 computation rule for 0, we need that 0 isn't the successor of any number: this
 prevents that we ever land in the successor case. For the computation rule for the
 successor, we also use that the successor is injective.

 Content
 1. Clauses of maps defined by recursion
 2. The formula defining the recursive map
 3. The recursive specification
 4. The recursive map satisfies the specification
 5. Computation rule for 0
 6. Computation rule for the successor

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HyperdoctrineNat.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.InductivePER.

Local Open Scope cat.
Local Open Scope hd.
Local Open Scope weak_tripos.

Section RecursiveMap.
  Context {H : weak_tripos}
          (N : first_order_hyperdoctrine_nats H)
          {X : partial_setoid H}
          (zX : partial_setoid_morphism (eq_partial_setoid 𝟙) X)
          (sX : partial_setoid_morphism X X).

  (** * 1. Clauses of maps defined by recursion *)
  Definition map_contains_z
    : form (ℙ (N ×h X))
    := let p := π₁ (tm_var (ℙ (N ×h X) ×h X)) in
       let x := π₂ (tm_var (ℙ (N ×h X) ×h X)) in
       (∀h (zX [ ⟨ !! , x ⟩ ]
            ⇒
            ⟨ hd_nats_z N _ , x ⟩ ∈ p)).

  Proposition map_contains_z_prf
              {Γ : ty H}
              {Δ : form Γ}
              (p : tm Γ (ℙ (N ×h X)))
              (x : tm Γ X)
              (q₁ : Δ ⊢ map_contains_z [ p ])
              (q₂ : Δ ⊢ zX [ ⟨ !! , x ⟩ ])
    : Δ ⊢ ⟨ hd_nats_z N _ , x ⟩ ∈ p.
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      exact (conj_intro q₁ q₂).
    }
    unfold map_contains_z.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      exact (forall_elim (hyperdoctrine_hyp _) x).
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    rewrite subst_hd_nats_z.
    refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Definition map_contains_s
    : form (ℙ (N ×h X))
    := let p := π₁ (π₁ (π₁ (tm_var _))) in
       let x := π₂ (π₁ (π₁ (tm_var _))) in
       let y := π₂ (π₁ (tm_var _)) in
       let n := π₂ (tm_var _) in
       (∀h ∀h ∀h (sX [ ⟨ x , y ⟩ ]
                  ⇒ ⟨ n , x ⟩ ∈ p
                  ⇒ ⟨ hd_nats_s N n , y ⟩ ∈ p)).

  Proposition map_contains_s_prf
              {Γ : ty H}
              {Δ : form Γ}
              (p : tm Γ (ℙ (N ×h X)))
              (x y : tm Γ X)
              (n : tm Γ N)
              (q₁ : Δ ⊢ map_contains_s [ p ])
              (q₂ : Δ ⊢ sX [ ⟨ x , y ⟩ ])
              (q₃ : Δ ⊢ ⟨ n , x ⟩ ∈ p)
    : Δ ⊢ ⟨ hd_nats_s N n , y ⟩ ∈ p.
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      exact (conj_intro q₁ (conj_intro q₂ q₃)).
    }
    unfold map_contains_s.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact x.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact y.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact n.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    hypersimplify.
    rewrite subst_hd_nats_s.
    rewrite !hyperdoctrine_pr2_subst.
    rewrite !var_tm_subst.
    rewrite !hyperdoctrine_pair_pr2.
    refine (impl_elim _ (impl_elim _ _)).
    - do 2 use weaken_right.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 2. The formula defining the recursive map *)
  Definition nat_per_rec_form_def
    : form (N ×h X)
    := let n := π₁ (π₁ (tm_var ((N ×h X) ×h ℙ (N ×h X)))) in
       let x := π₂ (π₁ (tm_var ((N ×h X) ×h ℙ (N ×h X)))) in
       let p := π₂ (tm_var ((N ×h X) ×h ℙ (N ×h X))) in
       (∀h (map_contains_z [ p ]
            ⇒ map_contains_s [ p ]
            ⇒ (exp_partial_setoid_eq_defined_law (nat_partial_setoid N) _) [ p ]
            ⇒ ⟨ n , x ⟩ ∈ p)).

  Definition nat_per_rec_form
    : form (N ×h X)
    := let n := π₁ (tm_var (nat_partial_setoid N ×h X)) in
       let x := π₂ (tm_var (N ×h X)) in
       n ~ n
       ∧
       x ~ x
       ∧
       nat_per_rec_form_def.

  (** * 3. The recursive specification *)
  Definition nat_per_rec_spec_suc
    : form (((N ×h X) ×h N) ×h X)
    := let Γ := ((N ×h X) ×h N) ×h X in
       let y := π₂ (tm_var Γ) in
       let m := π₂ (π₁ (tm_var Γ)) in
       let x := π₂ (π₁ (π₁ (tm_var Γ))) in
       let n := π₁ (π₁ (π₁ (tm_var Γ))) in
       (n ≡ hd_nats_s N m ∧ sX [ ⟨ y , x ⟩ ]
        ∧
        nat_per_rec_form [ ⟨ m , y ⟩ ]).

  Definition nat_per_rec_spec
    : form (N ×h X)
    := let n := π₁ (tm_var (N ×h X)) in
       let x := π₂ (tm_var (N ×h X)) in
       (n ≡ hd_nats_z N _ ∧ zX [ ⟨ !! , x ⟩ ])
       ∨
       (∃h ∃h nat_per_rec_spec_suc).

  Proposition nat_per_rec_spec_zero
              {Γ : ty H}
              (x : tm Γ X)
              {Δ : form Γ}
              (p : Δ ⊢ zX [⟨ !! , x ⟩])
    : Δ ⊢ nat_per_rec_spec [ ⟨ hd_nats_z N _ , x ⟩ ].
  Proof.
    unfold nat_per_rec_spec.
    hypersimplify.
    use disj_intro_left.
    cbn.
    rewrite subst_hd_nats_z.
    use conj_intro.
    - use hyperdoctrine_refl.
    - exact p.
  Qed.

  Proposition nat_per_rec_spec_s
              {Γ : ty H}
              {n : tm Γ N}
              (x sx : tm Γ X)
              {Δ : form Γ}
              (p : Δ ⊢ sX [⟨ x , sx ⟩])
              (q : Δ ⊢ nat_per_rec_form [⟨ n , x ⟩])
    : Δ ⊢ nat_per_rec_spec [ ⟨ hd_nats_s N n , sx ⟩ ].
  Proof.
    unfold nat_per_rec_spec.
    hypersimplify.
    use disj_intro_right.
    use exists_intro.
    {
      exact n.
    }
    hypersimplify.
    use exists_intro.
    {
      exact x.
    }
    unfold nat_per_rec_spec_suc.
    hypersimplify.
    rewrite subst_hd_nats_s.
    rewrite !hyperdoctrine_pr2_subst.
    rewrite !hyperdoctrine_pr1_subst.
    rewrite !var_tm_subst.
    rewrite !hyperdoctrine_pair_pr1.
    rewrite !hyperdoctrine_pair_pr2.
    repeat use conj_intro.
    - use hyperdoctrine_refl.
    - exact p.
    - exact q.
  Qed.

  Proposition nat_per_rec_spec_eq
              {Γ : ty H}
              {n₁ n₂ : tm Γ (nat_partial_setoid N)}
              {x₁ x₂ : tm Γ X}
              {Δ : form Γ}
              (p₁ : Δ ⊢ n₁ ~ n₂)
              (p₂ : Δ ⊢ x₁ ~ x₂)
              (p₃ : Δ ⊢ nat_per_rec_spec [⟨ n₁ , x₁ ⟩])
    : Δ ⊢ nat_per_rec_spec [⟨ n₂ , x₂ ⟩].
  Proof.
    refine (weaken_cut p₃ _).
    unfold nat_per_rec_spec.
    hypersimplify.
    use hyp_sym.
    refine (disj_elim _ _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_left.
      rewrite !subst_hd_nats_z.
      use conj_intro.
      + refine (hyperdoctrine_eq_trans _ _).
        {
          use weaken_left.
          use eq_nat_partial_setoid_to_eq.
          use partial_setoid_sym.
          exact p₁.
        }
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use hyp_rtrans.
        use (partial_setoid_mor_eq_defined zX _ _ (weaken_right (hyperdoctrine_hyp _) _)).
        * use eq_in_eq_partial_setoid.
          apply hyperdoctrine_refl.
        * do 2 use weaken_left.
          exact p₂.
    - use hyp_ltrans.
      use weaken_right.
      use disj_intro_right.
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
      pose (x := π₂ (tm_var ((Γ ×h N) ×h X))).
      pose (n := π₂ (π₁ (tm_var ((Γ ×h N) ×h X)))).
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h N) ×h X)))).
      fold x n γ.
      use exists_intro.
      {
        exact n.
      }
      hypersimplify.
      use exists_intro.
      {
        exact x.
      }
      hypersimplify.
      fold γ.
      unfold nat_per_rec_spec_suc.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      rewrite !hyperdoctrine_pr2_subst.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      rewrite !hyperdoctrine_pair_pr2.
      repeat use conj_intro.
      + refine (hyperdoctrine_eq_trans _ _).
        * rewrite <- (equal_subst γ _ n₁).
          use weaken_left.
          use hyperdoctrine_proof_subst.
          use hyperdoctrine_eq_sym.
          use eq_nat_partial_setoid_to_eq.
          exact p₁.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + refine (partial_setoid_mor_eq_defined sX _ _ _).
        * do 2 use weaken_right.
          use weaken_left.
          refine (partial_setoid_mor_dom_defined sX _ _ _).
          apply hyperdoctrine_hyp.
        * use weaken_left.
          refine (hyperdoctrine_cut _ _).
          {
            exact (hyperdoctrine_proof_subst γ p₂).
          }
          rewrite partial_setoid_subst.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + do 3 use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The recursive map satisfies the specification *)
  Proposition from_nat_per_rec_spec
    : nat_per_rec_spec ⊢ nat_per_rec_form.
  Proof.
    refine (disj_elim _ _ _).
    - apply hyperdoctrine_hyp.
    - use weaken_right.
      repeat use conj_intro.
      + cbn.
        pose (n := π₁ (tm_var (N ×h X))).
        pose (x := π₂ (tm_var (N ×h X))).
        fold n x.
        refine (hyperdoctrine_cut _ _).
        {
          use weaken_left.
          refine (hyperdoctrine_eq_transportb
                    (tm_var (nat_partial_setoid N) ~ tm_var _)
                    (hyperdoctrine_hyp _)
                    _).
          cbn.
          hypersimplify.
          use nat_partial_setoid_refl.
          apply is_inductive_zero.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      + cbn.
        pose (n := π₁ (tm_var (N ×h X))).
        pose (x := π₂ (tm_var (N ×h X))).
        fold n x.
        use weaken_right.
        refine (partial_setoid_mor_cod_defined zX _ _ _).
        apply hyperdoctrine_hyp.
      + use forall_intro.
        do 2 use impl_intro.
        cbn.
        hypersimplify.
        rewrite subst_hd_nats_z.
        pose (n := π₁ (π₁ (tm_var ((N ×h X) ×h ℙ (N ×h X))))).
        pose (x := π₂ (π₁ (tm_var ((N ×h X) ×h ℙ (N ×h X))))).
        pose (p := π₂ (tm_var ((N ×h X) ×h ℙ (N ×h X)))).
        fold n x p.
        use weaken_left.
        refine (weaken_cut _ _).
        {
          refine (map_contains_z_prf _ _ (weaken_right (hyperdoctrine_hyp _) _) _).
          use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        refine (hyperdoctrine_cut _ _).
        {
          refine (hyperdoctrine_eq_elim
                    (⟨ π₂ (tm_var _) , x [ π₁ (tm_var _) ]tm ⟩ ∈ p [ π₁ (tm_var _) ]tm)
                    _
                    _).
          {
            do 3 use weaken_left.
            apply hyperdoctrine_eq_sym.
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        use impl_intro.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - use weaken_right.
      refine (exists_elim _ _).
      {
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      refine (exists_elim _ _).
      {
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      unfold nat_per_rec_spec_suc, nat_per_rec_form ; cbn.
      hypersimplify.
      repeat use conj_intro.
      + pose (Γ := ((N ×h X) ×h N) ×h X).
        fold Γ.
        pose (y := π₂ (tm_var Γ)).
        pose (m := π₂ (π₁ (tm_var Γ))).
        pose (x := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (n := π₁ (π₁ (π₁ (tm_var Γ)))).
        cbn.
        fold n m x y.
        refine (hyperdoctrine_cut _ _).
        {
          refine (hyperdoctrine_eq_transportb
                    (tm_var (nat_partial_setoid N) ~ tm_var _)
                    (weaken_left (hyperdoctrine_hyp _) _)
                    _).
          cbn.
          hypersimplify.
          use nat_partial_setoid_refl.
          apply is_inductive_suc.
          use weaken_right.
          use weaken_right.
          use weaken_left.
          refine (eq_nat_partial_setoid_to_inductive _ _).
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      + pose (Γ := ((N ×h X) ×h N) ×h X).
        fold Γ.
        pose (y := π₂ (tm_var Γ)).
        pose (m := π₂ (π₁ (tm_var Γ))).
        pose (x := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (n := π₁ (π₁ (π₁ (tm_var Γ)))).
        fold n m x y.
        refine (partial_setoid_mor_cod_defined sX _ _ _).
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + unfold nat_per_rec_form_def.
        rewrite !forall_subst.
        use forall_intro.
        hypersimplify.
        rewrite subst_hd_nats_s.
        pose (Γ := (((N ×h X) ×h N) ×h X) ×h ℙ (N ×h X)).
        fold Γ.
        pose (p := π₂ (tm_var Γ)).
        pose (y := π₂ (π₁ (tm_var Γ))).
        pose (m := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (x := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (n := π₁ (π₁ (π₁ (π₁ (tm_var Γ))))).
        cbn.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !hyperdoctrine_pr1_subst.
        rewrite !var_tm_subst.
        fold n m x y p.
        do 3 use hyp_rtrans.
        use hyp_sym.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact p.
        }
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        fold m y.
        do 2 use impl_intro.
        refine (hyperdoctrine_cut _ _).
        {
          refine (conj_intro _ _).
          {
            do 3 use weaken_left.
            apply hyperdoctrine_hyp.
          }
          refine (conj_intro _ _).
          {
            refine (impl_elim _ _).
            {
              use weaken_right.
              apply hyperdoctrine_hyp.
            }
            refine (impl_elim _ _).
            {
              use weaken_left.
              use weaken_right.
              apply hyperdoctrine_hyp.
            }
            do 2 use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          }
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use hyp_rtrans.
        use hyp_sym.
        use impl_intro.
        refine (weaken_cut _ _).
        {
          refine (map_contains_s_prf _ _ _ _ _ _ _).
          - do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          - use weaken_left.
            use weaken_right.
            do 3 use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          - refine (impl_elim (weaken_right (hyperdoctrine_hyp _) _) _).
            use weaken_left.
            do 2 use weaken_right.
            apply hyperdoctrine_hyp.
        }
        refine (hyperdoctrine_cut _ _).
        {
          refine (hyperdoctrine_eq_elim
                    (⟨ π₂ (tm_var _) , x [ π₁ (tm_var _) ]tm ⟩ ∈ p [ π₁ (tm_var _) ]tm)
                    _
                    _).
          {
            do 2 use weaken_left.
            use weaken_right.
            do 4 use weaken_left.
            apply hyperdoctrine_eq_sym.
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition to_nat_per_rec_spec
    : nat_per_rec_form ⊢ nat_per_rec_spec.
  Proof.
    use hyp_rtrans.
    use hyp_sym.
    refine (exists_elim _ _).
    {
      exact (weak_tripos_compr (nat_per_rec_spec [ π₁ (tm_var _) ]) _ !!).
    }
    unfold nat_per_rec_form, nat_per_rec_form_def.
    cbn.
    hypersimplify.
    pose (Γ := (N ×h X) ×h ℙ (N ×h X)).
    fold Γ.
    pose (p := π₂ (tm_var Γ)).
    pose (x := π₂ (π₁ (tm_var Γ))).
    pose (n := π₁ (π₁ (tm_var Γ))).
    cbn.
    fold n x p.
    use hyp_ltrans.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      exact (forall_elim (hyperdoctrine_hyp _) p).
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    rewrite hyperdoctrine_unit_tm_subst.
    fold n x.
    refine (hyperdoctrine_cut _ _).
    - refine (weak_tripos_rel_equiv_left _ _ _ _ _ _ _).
      {
        use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      refine (impl_elim
                _
                (impl_elim
                   _
                   (impl_elim
                      _
                      (weaken_right (hyperdoctrine_hyp _) _)))).
      + use weaken_left.
        unfold p, n, x, Γ.
        clear Γ n x p.
        unfold exp_partial_setoid_eq_defined_law.
        cbn.
        hypersimplify_form.
        do 4 use forall_intro.
        hypersimplify.
        pose (Γ := (((((N ×h X) ×h ℙ (N ×h X)) ×h N) ×h N) ×h X) ×h X).
        fold Γ.
        pose (x₂ := π₂ (tm_var Γ)).
        pose (x₁ := π₂ (π₁ (tm_var Γ))).
        pose (n₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (n₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (f := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (x₃ := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))).
        pose (n₃ := π₁ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))).
        cbn.
        fold x₁ x₂ x₃ n₁ n₂ n₃ f.
        use weaken_right.
        do 3 use impl_intro.
        unfold weak_tripos_rel_equiv.
        hypersimplify.
        do 2 use hyp_ltrans.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact ⟨ n₁ , x₁ ⟩.
        }
        use hyp_ltrans.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact ⟨ n₂ , x₂ ⟩.
        }
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        fold f.
        refine (iff_elim_right _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        refine (weaken_cut _ _).
        {
          refine (iff_elim_left _ _).
          {
            use weaken_right.
            apply hyperdoctrine_hyp.
          }
          use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use nat_per_rec_spec_eq.
        * exact n₁.
        * exact x₁.
        * do 3 use weaken_left.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_left.
          use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        unfold map_contains_s.
        hypersimplify.
        do 3 use forall_intro.
        unfold p, n, x, Γ.
        hypersimplify.
        clear Γ p n x.
        pose (Γ := ((((N ×h X) ×h ℙ (N ×h X)) ×h X) ×h X) ×h N).
        pose (m := π₂ (tm_var Γ)).
        pose (x₃ := π₂ (π₁ (tm_var Γ))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (p := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (n := π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        cbn.
        fold Γ n m x₁ x₂ x₃ p.
        use hyp_sym.
        do 2 use impl_intro.
        do 2 use hyp_ltrans.
        rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !var_tm_subst.
        rewrite !hyperdoctrine_pair_pr2.
        unfold weak_tripos_rel_equiv.
        hypersimplify.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact ⟨ hd_nats_s N m , x₃ ⟩.
        }
        hypersimplify.
        fold p.
        refine (iff_elim_right _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact ⟨ m , x₂ ⟩.
        }
        hypersimplify.
        fold p.
        use hyp_ltrans.
        refine (hyperdoctrine_cut _ _).
        {
          use weaken_right.
          refine (conj_intro _ _).
          {
            use weaken_left.
            use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          }
          refine (iff_elim_left (weaken_right (hyperdoctrine_hyp _) _) _).
          use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use nat_per_rec_spec_s.
        * exact x₂.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          refine (hyperdoctrine_proof_subst _ _).
          apply from_nat_per_rec_spec.
      + use weaken_left.
        unfold map_contains_z.
        hypersimplify.
        use forall_intro.
        unfold p, n, x, Γ.
        hypersimplify.
        clear Γ p n x.
        pose (Γ := ((N ×h X) ×h ℙ (N ×h X)) ×h X).
        pose (y := π₂ (tm_var Γ)).
        pose (p := π₂ (π₁ (tm_var Γ))).
        pose (x := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (n := π₁ (π₁ (π₁ (tm_var Γ)))).
        cbn.
        fold Γ n x y p.
        use impl_intro.
        unfold weak_tripos_rel_equiv.
        hypersimplify.
        rewrite subst_hd_nats_z.
        use hyp_ltrans.
        use hyp_sym.
        use hyp_ltrans.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact ⟨ hd_nats_z N Γ , y ⟩.
        }
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        fold p.
        use hyp_sym.
        refine (iff_elim_right _ _).
        {
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        use weaken_right.
        unfold nat_per_rec_spec.
        hypersimplify.
        cbn.
        rewrite !subst_hd_nats_z.
        use disj_intro_left.
        use conj_intro.
        * apply hyperdoctrine_refl.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - hypersimplify.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var Γ))).
      fold n x.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition nat_per_rec_spec_iff
    : ⊤ ⊢ nat_per_rec_form ⇔ nat_per_rec_spec.
  Proof.
    use iff_intro.
    - use weaken_right.
      exact to_nat_per_rec_spec.
    - use weaken_right.
      exact from_nat_per_rec_spec.
  Qed.

  (** * 5. Computation rule for 0 *)
  Proposition nat_per_rec_form_z
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              (p : Δ ⊢ zX [ ⟨ !! , x ⟩ ])
    : Δ ⊢ nat_per_rec_form [ ⟨ hd_nats_z N _ , x ⟩ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_proof_subst _ from_nat_per_rec_spec)).
    unfold nat_per_rec_spec.
    hypersimplify_form.
    use disj_intro_left.
    hypersimplify.
    cbn.
    rewrite subst_hd_nats_z.
    use conj_intro.
    - apply hyperdoctrine_refl.
    - apply hyperdoctrine_hyp.
  Qed.

  Proposition nat_per_rec_form_z_inv
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              (p : Δ ⊢ nat_per_rec_form [ ⟨ hd_nats_z N _ , x ⟩ ])
    : Δ ⊢ zX [ ⟨ !! , x ⟩ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_proof_subst _ _).
      apply to_nat_per_rec_spec.
    }
    unfold nat_per_rec_spec.
    hypersimplify.
    cbn.
    rewrite subst_hd_nats_z.
    refine (disj_elim (hyperdoctrine_hyp _) _ _).
    - do 2 use weaken_right.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      refine (exists_elim (hyperdoctrine_hyp _) _).
      use weaken_right.
      refine (exists_elim (hyperdoctrine_hyp _) _).
      use weaken_right.
      unfold nat_per_rec_spec_suc.
      hypersimplify.
      rewrite subst_hd_nats_z.
      rewrite subst_hd_nats_s.
      refine (neg_elim _ _).
      + use weaken_left.
        refine (hyperdoctrine_eq_sym _).
        apply hyperdoctrine_hyp.
      + apply first_order_hyperdoctrine_nats_z_neq_s.
  Qed.

  (** * 6. Computation rule for the successor *)
  Proposition nat_per_rec_form_s
              {Γ : ty H}
              {Δ : form Γ}
              {n : tm Γ N}
              {x sx : tm Γ X}
              (q₁ : Δ ⊢ sX [ ⟨ x , sx ⟩ ])
              (q₂ : Δ ⊢ nat_per_rec_form [ ⟨ n , x ⟩ ])
    : Δ ⊢ nat_per_rec_form [ ⟨ hd_nats_s N n , sx ⟩ ].
  Proof.
    refine (hyperdoctrine_cut (conj_intro q₁ q₂) _).
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_proof_subst _ from_nat_per_rec_spec)).
    refine (nat_per_rec_spec_s _ _ _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition nat_per_rec_form_s_inv
              {Γ : ty H}
              {Δ : form Γ}
              {n : tm Γ N}
              {sx : tm Γ X}
              (q : Δ ⊢ nat_per_rec_form [ ⟨ hd_nats_s N n , sx ⟩ ])
    : Δ ⊢ (∃h (sX [ ⟨ π₂ (tm_var _) , sx [ π₁ (tm_var _) ]tm ⟩ ]
               ∧
               nat_per_rec_form [ ⟨ n [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ])).
  Proof.
    refine (hyperdoctrine_cut q _).
    refine (hyperdoctrine_cut
              (hyperdoctrine_proof_subst _ to_nat_per_rec_spec)
              _).
    unfold nat_per_rec_spec.
    hypersimplify.
    cbn.
    rewrite subst_hd_nats_z.
    refine (disj_elim (hyperdoctrine_hyp _) _ _).
    - use weaken_right.
      use weaken_left.
      refine (first_order_hyperdoctrine_nats_z_neq_s_all _ _ _).
      apply hyperdoctrine_hyp.
    - use weaken_right.
      refine (exists_elim (hyperdoctrine_hyp _) _).
      use weaken_right.
      refine (exists_elim (hyperdoctrine_hyp _) _).
      use weaken_right.
      unfold nat_per_rec_spec_suc.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      cbn.
      rewrite !hyperdoctrine_pr2_subst.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      rewrite !hyperdoctrine_pair_pr2.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      use conj_intro.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_cut _ _).
        {
          refine (hyperdoctrine_eq_elim
                    (nat_per_rec_form [⟨ π₂ (tm_var _) , π₂ (π₁ (tm_var _)) ⟩])
                    _
                    _).
          {
            use weaken_left.
            use hyperdoctrine_eq_sym.
            exact (first_order_hyperdoctrine_nats_s_mono N (hyperdoctrine_hyp _)).
          }
          hypersimplify.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
  Qed.
End RecursiveMap.
