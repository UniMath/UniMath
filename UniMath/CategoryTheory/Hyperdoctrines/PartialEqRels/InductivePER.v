(**

 Inductive sets

 Our goal is to define a natural numbers object in the topos associated to a tripos.
 To do so, we assume that the tripos comes with an object `N` with terms `z : N` and
 `s : N → N` such that `z ≠ s n` and `s` is injective. From the object `N`, we can
 make the natural numbers object using an impredicative encoding. Specifically, `N`
 induces a partial setois `(N, ≡)` and we restrict that partial setoid to the
 inductively generated elements. These are the elements for which the induction
 principle of natural numbers hold.

 The reason why it is necessary to take this encoding, is because the object `N`
 might be too 'large': there might be too amny terms of type `N` meaning that we do
 not get a NNO. It is also worthwhile to note the similarity with the construction
 of natural numbers in ZFC. The axiom of infinity usually states that there is an
 infinite set, and we can construct the set of natural numbers by aking the
 intersection of all inductive sets.

 Finally, we give a principle that allows us to check whether two morphisms from
 `N` to some other partial setoid are equal. This principle is based on induction.

 Content
 1, Preliminary notions
 2. Inductive numbers
 3. Induction principles
 4. Examples of inductive numbers
 5. The PER of natural numbers
 6. Equality of morphisms

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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
Require Export UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.

Local Open Scope cat.
Local Open Scope hd.
Local Open Scope weak_tripos.

Section InductivePER.
  Context {H : weak_tripos}
          (N : first_order_hyperdoctrine_nats H).

  (** * 1, Preliminary notions *)
  Definition contains_zero
    : form (ℙ N)
    := hd_nats_z N _ ∈ tm_var _.

  Definition closed_suc
    : form (ℙ N)
    := let p := π₁ (tm_var (ℙ N ×h N)) in
       let n := π₂ (tm_var (ℙ N ×h N)) in
       (∀h (n ∈ p ⇒ hd_nats_s N n ∈ p)).

  Proposition closed_suc_on_suc
              {Γ : ty H}
              {Δ : form Γ}
              {p : tm Γ (ℙ N)}
              {n : tm Γ N}
              (q₁ : Δ ⊢ closed_suc [ p ])
              (q₂ : Δ ⊢ n ∈ p)
    : Δ ⊢ hd_nats_s N n ∈ p.
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      exact (conj_intro q₁ q₂).
    }
    unfold closed_suc.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact n.
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    rewrite subst_hd_nats_s.
    rewrite !hyperdoctrine_pr2_subst.
    rewrite !var_tm_subst.
    rewrite !hyperdoctrine_pair_pr2.
    refine (impl_elim _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 2. Inductive numbers *)
  Definition is_inductive_nat
    : form N
    := let n := π₁ (tm_var (N ×h ℙ N)) in
       let p := π₂ (tm_var (N ×h ℙ N)) in
       (∀h (contains_zero [ p ] ⇒ closed_suc [ p ] ⇒ n ∈ p)).

  (** * 3. Induction principles *)
  Proposition is_inductive_nat_contained
              {Γ : ty H}
              {Δ : form Γ}
              {n : tm Γ N}
              {p : tm Γ (ℙ N)}
              (q₁ : Δ ⊢ contains_zero [ p ])
              (q₂ : Δ ⊢ closed_suc [ p ])
              (q₃ : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ n ∈ p.
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      refine (conj_intro q₃ _).
      exact (conj_intro q₁ q₂).
    }
    unfold is_inductive_nat.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact p.
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    refine (impl_elim _ _).
    {
      use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    }
    refine (impl_elim _ _).
    {
      do 2 use weaken_left.
      apply hyperdoctrine_hyp.
    }
    use weaken_right.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition is_inductive_nat_induction
              {Γ : ty H}
              {Δ : form Γ}
              {φ : form (N ×h Γ)}
              {n : tm Γ N}
              (q₁ : Δ ⊢ φ [ ⟨ hd_nats_z N _ , tm_var _ ⟩ ])
              (q₂ : Δ ⊢ ∀h (φ [ ⟨ π₂ (tm_var _) , π₁ (tm_var _) ⟩ ]
                            ⇒
                            φ [ ⟨ hd_nats_s N (π₂ (tm_var _)) , π₁ (tm_var _) ⟩ ]))
              (q₃ : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ φ [ ⟨ n , tm_var _ ⟩ ].
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      exact (conj_intro q₁ (conj_intro q₂ q₃)).
    }
    refine (exists_elim _ _).
    {
      exact (weak_tripos_compr φ _ (tm_var _)).
    }
    hypersimplify.
    rewrite var_tm_subst.
    refine (weak_tripos_rel_equiv_left _ _ _ _ _ _ _).
    {
      use weaken_right.
      apply hyperdoctrine_hyp.
    }
    use is_inductive_nat_contained.
    - unfold contains_zero.
      hypersimplify.
      rewrite !subst_hd_nats_z.
      refine (weak_tripos_rel_equiv_right _ _ _ _ _ _ _).
      {
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      do 2 use weaken_left.
      apply hyperdoctrine_hyp.
    - use hyp_ltrans.
      use weaken_right.
      use hyp_ltrans.
      unfold closed_suc.
      hypersimplify.
      use forall_intro.
      use impl_intro.
      hypersimplify.
      use hyp_ltrans.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (tm_var _)).
      }
      use hyp_ltrans.
      use weaken_right.
      do 2 use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      rewrite !subst_hd_nats_s.
      rewrite !hyperdoctrine_pr2_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr2.
      unfold weak_tripos_rel_equiv.
      hypersimplify.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (hd_nats_s N (π₂ (tm_var _))).
      }
      hypersimplify.
      refine (iff_elim_right _ _).
      {
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      use weaken_left.
      use hyp_rtrans.
      refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (forall_elim (hyperdoctrine_hyp _) _).
        exact (π₂ (tm_var _)).
      }
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      refine (iff_elim_left _ _).
      {
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      do 2 use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 4. Examples of inductive numbers *)
  Proposition is_inductive_zero
              {Γ : ty H}
              (Δ : form Γ)
    : Δ ⊢ is_inductive_nat [ hd_nats_z N Γ ].
  Proof.
    unfold is_inductive_nat.
    hypersimplify.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use weaken_left.
    unfold contains_zero.
    hypersimplify.
    rewrite !subst_hd_nats_z.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition is_inductive_suc
              {Γ : ty H}
              (n : tm Γ N)
              {Δ : form Γ}
              (p : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ is_inductive_nat [ hd_nats_s N n ].
  Proof.
    unfold is_inductive_nat.
    hypersimplify.
    use forall_intro.
    do 2 use impl_intro.
    rewrite subst_hd_nats_s.
    refine (closed_suc_on_suc _ _).
    {
      use weaken_right.
      apply hyperdoctrine_hyp.
    }
    use hyp_ltrans.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      exact (hyperdoctrine_proof_subst _ p).
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    use is_inductive_nat_contained.
    - do 2 use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  (** * 5. The PER of natural numbers *)
  Definition nat_per_form
    : form (N ×h N)
    := let n := π₁ (tm_var (N ×h N)) in
       let m := π₂ (tm_var (N ×h N)) in
       n ≡ m ∧ is_inductive_nat [ n ].

  Arguments nat_per_form /.

  Proposition nat_per_axioms
    : per_axioms nat_per_form.
  Proof.
    split.
    - do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      hypersimplify.
      pose (n := π₂ (π₁ (tm_var ((𝟙 ×h N) ×h N)))).
      pose (m := π₂ (tm_var ((𝟙 ×h N) ×h N))).
      fold n m.
      use conj_intro.
      + use weaken_left.
        use hyperdoctrine_eq_sym.
        apply hyperdoctrine_hyp.
      + refine (hyperdoctrine_eq_transportf _ _ _).
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      hypersimplify.
      pose (n₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h N) ×h N) ×h N))))).
      pose (n₂ := π₂ (π₁ (tm_var (((𝟙 ×h N) ×h N) ×h N)))).
      pose (n₃ := π₂ (tm_var (((𝟙 ×h N) ×h N) ×h N))).
      fold n₁ n₂ n₃.
      use conj_intro.
      + use hyperdoctrine_eq_trans.
        * exact n₂.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition nat_per
    : per N.
  Proof.
    use make_per.
    - exact nat_per_form.
    - exact nat_per_axioms.
  Defined.

  Definition nat_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact N.
    - exact nat_per.
  Defined.

  Proposition eq_in_nat_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {n m : tm Γ nat_partial_setoid}
              (p : Δ ⊢ n ≡ m)
              (q : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ n ~ m.
  Proof.
    unfold partial_setoid_formula.
    cbn.
    hypersimplify.
    use conj_intro.
    - exact p.
    - exact q.
  Qed.

  Proposition nat_partial_setoid_refl
              {Γ : ty H}
              {Δ : form Γ}
              {n : tm Γ nat_partial_setoid}
              (p : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ n ~ n.
  Proof.
    use eq_in_nat_partial_setoid.
    - apply hyperdoctrine_refl.
    - exact p.
  Qed.

  Proposition eq_nat_partial_setoid_to_eq
              {Γ : ty H}
              {Δ : form Γ}
              {n m : tm Γ nat_partial_setoid}
              (p : Δ ⊢ n ~ m)
    : Δ ⊢ n ≡ m.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula.
    cbn.
    hypersimplify.
    refine (conj_elim_left _).
    apply hyperdoctrine_hyp.
  Qed.

  Proposition eq_nat_partial_setoid_to_inductive
              {Γ : ty H}
              {Δ : form Γ}
              {n m : tm Γ nat_partial_setoid}
              (p : Δ ⊢ n ~ m)
    : Δ ⊢ is_inductive_nat [ n ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula.
    cbn.
    hypersimplify.
    refine (conj_elim_right _).
    apply hyperdoctrine_hyp.
  Qed.

  Proposition eq_nat_partial_setoid_to_inductive'
              {Γ : ty H}
              {Δ : form Γ}
              {n m : tm Γ nat_partial_setoid}
              (p : Δ ⊢ n ~ m)
    : Δ ⊢ is_inductive_nat [ m ].
  Proof.
    refine (eq_nat_partial_setoid_to_inductive _).
    use partial_setoid_sym.
    exact p.
  Qed.

  (** * 6. Equality of morphisms *)
  Proposition is_inductive_nat_induction_closed
              {Γ : ty H}
              {Δ : form Γ}
              {φ : form N}
              {n : tm Γ N}
              (q₁ : Δ ⊢ φ [ hd_nats_z N _ ])
              (q₂ : Δ ⊢ ∀h ((π₂ (tm_var (_ ×h nat_partial_setoid)) ~ π₂ (tm_var _))
                            ⇒
                            φ [ π₂ (tm_var _) ]
                            ⇒
                            φ [ hd_nats_s N (π₂ (tm_var _)) ]))
              (q₃ : Δ ⊢ is_inductive_nat [ n ])
    : Δ ⊢ φ [ n ].
  Proof.
    pose (@is_inductive_nat_induction
            _
            Δ
            ((π₁ (tm_var (nat_partial_setoid ×h _)) ~ π₁ (tm_var _))
             ∧
             φ [ π₁ (tm_var _) ])
            n) as r.
    refine (hyperdoctrine_cut (r _ _ q₃) _).
    - hypersimplify.
      use conj_intro.
      + use nat_partial_setoid_refl.
        apply is_inductive_zero.
      + exact q₁.
    - hypersimplify.
      use forall_intro.
      refine (hyperdoctrine_cut _ _).
      {
        refine (forall_elim _ (π₂ (tm_var _))).
        refine (hyperdoctrine_cut
                  (hyperdoctrine_proof_subst _ q₂)
                  _).
        hypersimplify.
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      use impl_intro.
      use conj_intro.
      + use nat_partial_setoid_refl.
        use is_inductive_suc.
        use weaken_right.
        use weaken_left.
        refine (eq_nat_partial_setoid_to_inductive _).
        apply hyperdoctrine_hyp.
      + rewrite subst_hd_nats_s.
        rewrite !hyperdoctrine_pr2_subst.
        rewrite !var_tm_subst.
        rewrite hyperdoctrine_pair_pr2.
        refine (impl_elim _ (impl_elim _ (weaken_left (hyperdoctrine_hyp _) _))).
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
    - hypersimplify.
      use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_mor_contains_Z
             {X : partial_setoid H}
             (φ ψ : form (N ×h X))
    : form (N ×h X)
    := φ [⟨ hd_nats_z N (N ×h X) , π₂ (tm_var (N ×h X)) ⟩]
       ⇒
       ψ [⟨ hd_nats_z N (N ×h X) , π₂ (tm_var (N ×h X)) ⟩].

  Definition partial_setoid_mor_contains_S
             {X : partial_setoid H}
             (φ ψ : form (N ×h X))
    : form (N ×h X)
    := (∃h (φ [ ⟨ π₁ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩ ]
            ∧
            ψ [ ⟨ π₁ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩ ]))
       ⇒
       φ [ ⟨ hd_nats_s N (π₁ (tm_var _)) , π₂ (tm_var _) ⟩ ]
       ⇒
       ψ [ ⟨ hd_nats_s N (π₁ (tm_var _)) , π₂ (tm_var _) ⟩ ].

  Proposition eq_nat_partial_setoid_morphism_lem
              {X : partial_setoid H}
              (φ : partial_setoid_morphism nat_partial_setoid X)
              (ψ : form (N ×h X))
              (Δ : form N)
              (pZ : ⊤ ⊢ partial_setoid_mor_contains_Z φ ψ)
              (pS : ⊤ ⊢ partial_setoid_mor_contains_S φ ψ)
              (pI : Δ ⊢ is_inductive_nat)
    : Δ ⊢ (∀h (φ ⇒ ψ)) [ tm_var _ ].
  Proof.
    use is_inductive_nat_induction_closed.
    - cbn.
      hypersimplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      rewrite subst_hd_nats_z.
      refine (hyperdoctrine_cut _ _).
      {
        refine (conj_intro
                  _
                  (hyperdoctrine_hyp _)).
        refine (hyperdoctrine_cut _ pZ).
        apply truth_intro.
      }
      refine (impl_elim _ _).
      {
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      use weaken_left.
      apply hyperdoctrine_hyp.
    - hypersimplify.
      use forall_intro.
      do 2 use impl_intro.
      use forall_intro.
      use impl_intro.
      hypersimplify.
      rewrite subst_hd_nats_s.
      rewrite !hyperdoctrine_pr2_subst.
      rewrite !var_tm_subst.
      refine (impl_elim _ _).
      {
        use weaken_right.
        apply hyperdoctrine_hyp.
      }
      use weaken_left.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        refine (hyperdoctrine_cut
                  _
                  (hyperdoctrine_proof_subst
                     ⟨ π₂ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩
                     pS)).
        hypersimplify.
        apply truth_intro.
      }
      do 2 use hyp_ltrans.
      use weaken_right.
      unfold partial_setoid_mor_contains_S.
      hypersimplify.
      cbn.
      rewrite subst_hd_nats_s.
      rewrite !hyperdoctrine_pr1_subst.
      rewrite !var_tm_subst.
      rewrite !hyperdoctrine_pair_pr1.
      use hyp_rtrans.
      refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      refine (exists_elim _ _).
      {
        use weaken_left.
        refine (partial_setoid_mor_hom_exists φ _).
        apply hyperdoctrine_hyp.
      }
      hypersimplify.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      hypersimplify.
      use conj_intro.
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + use hyp_ltrans.
        use weaken_right.
        refine (weaken_cut _ _).
        {
          use weaken_left.
          refine (forall_elim (hyperdoctrine_hyp _) _).
          exact (π₂ (tm_var _)).
        }
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        refine (impl_elim _ _).
        {
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        use weaken_right.
        apply hyperdoctrine_hyp.
    - hypersimplify.
      exact pI.
  Qed.

  Proposition eq_nat_partial_setoid_morphism
              {X : partial_setoid H}
              {φ : partial_setoid_morphism nat_partial_setoid X}
              {ψ : form (N ×h X)}
              (pZ : ⊤ ⊢ partial_setoid_mor_contains_Z φ ψ)
              (pS : ⊤ ⊢ partial_setoid_mor_contains_S φ ψ)
    : φ ⊢ ψ.
  Proof.
    refine (weaken_cut _ _).
    - refine (hyperdoctrine_cut
                _
                (hyperdoctrine_proof_subst
                   (π₁ (tm_var _))
                   (eq_nat_partial_setoid_morphism_lem
                      φ ψ
                      (tm_var nat_partial_setoid ~ tm_var _)
                      _ _ _))).
      + hypersimplify.
        refine (partial_setoid_mor_dom_defined φ _ (π₂ (tm_var _)) _).
        rewrite <- hyperdoctrine_pair_eta.
        hypersimplify.
        apply hyperdoctrine_hyp.
      + exact pZ.
      + exact pS.
      + rewrite <- (hyperdoctrine_id_subst is_inductive_nat).
        refine (eq_nat_partial_setoid_to_inductive _).
        apply hyperdoctrine_hyp.
    - hypersimplify.
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
      rewrite <- !hyperdoctrine_pair_eta.
      hypersimplify.
      refine (impl_elim _ _).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.
End InductivePER.
