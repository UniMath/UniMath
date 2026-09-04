(**

 Logic in the presheaf model

 Since presheaves form a topos, the presheaf model of type theory gives rise to a model
 of higher-order logic. One nice aspect about this model is that we can give nice and
 concrete descriptions of the connectives, and in particular, we can check the validity
 of logical statements using Kripke-Joyal semantics. In this file, we establish the basic
 facts about logic in the presheaf model. We define predicate via terms of the subobject
 classifier and we simplify the description of each of the connectives. Finally, we
 describe the forcing relation used in Kripke-Joyal semantics.

 Content
 1. Preliminary operations
 2. Predicates and entailment in the presheaf model
 3. The truth formula
 4. The falsity formula
 5. Conjunction
 6. Disjunction
 7. Implication
 8. Universal quantification
 9. Existential quantification
 10. Equality
 11. The forcing relation
 12. Properties of the forcing relation

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.

Local Open Scope cat.

Declare Scope psh.
Delimit Scope psh with psh.

(** * 1. Preliminary operations *)
Definition presheaf_product
           {C : category}
           (Γ₁ Γ₂ : C^op ⟶ HSET)
  : C^op ⟶ HSET
  := BinProduct_of_functors C^op SET BinProductsHSET Γ₁ Γ₂.

Notation "Γ₁ ×P Γ₂" := (presheaf_product Γ₁ Γ₂) (at level 75) : psh.

Definition pr1_presheaf
           {C : category}
           (Γ₁ Γ₂ : C^op ⟶ HSET)
  : (Γ₁ ×P Γ₂)%psh ⟹ Γ₁
  := binproduct_nat_trans_pr1 _ _ _ _ _.

Definition pr2_presheaf
           {C : category}
           (Γ₁ Γ₂ : C^op ⟶ HSET)
  : (Γ₁ ×P Γ₂)%psh ⟹ Γ₂
  := binproduct_nat_trans_pr2 _ _ _ _ _.

Notation "'π₁'" := (pr1_presheaf _ _) : psh.
Notation "'π₂'" := (pr2_presheaf _ _) : psh.

Definition pair_presheaf
           {C : category}
           {Γ Δ₁ Δ₂ : C^op ⟶ HSET}
           (τ₁ : Γ ⟹ Δ₁)
           (τ₂ : Γ ⟹ Δ₂)
  : Γ ⟹ (Δ₁ ×P Δ₂)%psh
  := binproduct_nat_trans _ _ _ _ _ _ τ₁ τ₂.

Notation "⟨ τ₁ , τ₂ ⟩" := (pair_presheaf τ₁ τ₂) : psh.

Section PresheafLogic.
  Context {C : category}.

  Local Open Scope psh.

  (** * 2. Predicates and entailment in the presheaf model *)
  Definition presheaf_predicate
             (Γ : C^op ⟶ HSET)
    : UU
    := psh_term (dep_psh_subobject_classifier_ob Γ).

  Identity Coercion presheaf_predicate_to_term : presheaf_predicate >-> psh_term.

  Definition presheaf_predicate_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (φ : presheaf_predicate Γ₂)
    : presheaf_predicate Γ₁
    := psh_term_subst s φ.

  Local Notation "φ [ s ]" := (presheaf_predicate_subst s φ) : psh.

  Definition presheaf_predicate_entails
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : UU
    := ∀ (x y : C)
         (f : y --> x)
         (xx : (Γ x : hSet)),
       ((φ x xx : sieve x) y f ⇒ (ψ x xx : sieve x) y f)%logic.

  Local Notation "φ ⊢ ψ" := (presheaf_predicate_entails φ ψ) : psh.

  (** * 3. The truth formula *)
  Definition truth_presheaf_predicate
             (Γ : C^op ⟶ HSET)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (λ x xx, truth_sieve x).
    - abstract
        (intros x₁ x₂ f xx ; cbn ;
         use sieve_eq ;
         intros ;
         exact tt).
  Defined.

  Local Notation "⊤" := (truth_presheaf_predicate _) : psh.

  Proposition truth_presheaf_intro
              {Γ : C^op ⟶ HSET}
              (φ : presheaf_predicate Γ)
    : φ ⊢ ⊤.
  Proof.
    intros x y f xx p ; cbn.
    exact tt.
  Qed.

  Proposition truth_presheaf_subst
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
    : ⊤ ⊢ ⊤ [ s ].
  Proof.
    intros x y f xx _.
    exact tt.
  Qed.

  (** * 4. The falsity formula *)
  Definition false_sieve
             (x : C)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, hfalse).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p a ;
         induction a).
  Defined.

  Definition false_presheaf_predicate
             (Γ : C^op ⟶ HSET)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (λ x xx, false_sieve x).
    - abstract
        (intros x₁ x₂ f xx ; cbn ;
         use sieve_eq ;
         intros ? ? z ;
         induction z).
  Defined.

  Local Notation "⊥" := (false_presheaf_predicate _) : psh.

  Proposition false_presheaf_elim
              {Γ : C^op ⟶ HSET}
              (φ : presheaf_predicate Γ)
    : ⊥ ⊢ φ.
  Proof.
    intros x y f xx p ; cbn in p.
    induction p.
  Qed.

  Proposition false_presheaf_subst
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
    : ⊥ [ s ] ⊢ ⊥.
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 5. Conjunction *)
  Definition conj_sieve
             {x : C}
             (ω₁ ω₂ : sieve x)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, ω₁ y f ∧ ω₂ y f).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p [ q₁ q₂ ] ;
         exact (#ω ω₁ _ p q₁ ,, #ω ω₂ _ p q₂)).
  Defined.

  Definition conj_presheaf_predicate_data
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : psh_term_data (dep_psh_subobject_classifier_ob Γ)
    := λ x xx, conj_sieve (φ x xx) (ψ x xx).

  Arguments conj_presheaf_predicate_data /.

  Proposition conj_presheaf_predicate_law
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : psh_term_law (conj_presheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use sieve_eq ; cbn.
    - intros y g [ p₁ p₂ ].
      split.
      + use (from_sieve_eq_l (psh_term_naturality φ f xx) g).
        exact p₁.
      + use (from_sieve_eq_l (psh_term_naturality ψ f xx) g).
        exact p₂.
    - intros y g [ p₁ p₂ ].
      split.
      + use (from_sieve_eq_r (psh_term_naturality φ f xx) g).
        exact p₁.
      + use (from_sieve_eq_r (psh_term_naturality ψ f xx) g).
        exact p₂.
  Qed.

  Definition conj_presheaf_predicate
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (conj_presheaf_predicate_data φ ψ).
    - exact (conj_presheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ∧ ψ" := (conj_presheaf_predicate φ ψ) : psh.

  Proposition conj_presheaf_intro
              {Γ : C^op ⟶ HSET}
              {φ ψ χ : presheaf_predicate Γ}
              (p : χ ⊢ φ)
              (q : χ ⊢ ψ)
    : χ ⊢ φ ∧ ψ.
  Proof.
    intros x y f xx r ; cbn.
    exact (p x y f xx r ,, q x y f xx r).
  Qed.

  Proposition conj_presheaf_elim_l
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : φ ∧ ψ ⊢ φ.
  Proof.
    intros x y f xx r ; cbn in r.
    exact (pr1 r).
  Qed.

  Proposition conj_presheaf_elim_r
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : φ ∧ ψ ⊢ ψ.
  Proof.
    intros x y f xx r ; cbn in r.
    exact (pr2 r).
  Qed.

  Proposition conj_presheaf_subst
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
              (φ ψ : presheaf_predicate Γ₂)
    : φ [ s ] ∧ ψ [ s ] ⊢ (φ ∧ ψ) [ s ].
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 6. Disjunction *)
  Definition disj_sieve
             {x : C}
             (ω₁ ω₂ : sieve x)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, ω₁ y f ∨ ω₂ y f).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p ;
         use factor_through_squash_hProp ;
         intros [ z | z ] ;
         [ use hdisj_in1 ;
           exact (#ω ω₁ _ p z)
         | use hdisj_in2 ;
           exact (#ω ω₂ _ p z) ]).
  Defined.

  Definition disj_presheaf_predicate_data
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : psh_term_data (dep_psh_subobject_classifier_ob Γ)
    := λ x xx, disj_sieve (φ x xx) (ψ x xx).

  Arguments disj_presheaf_predicate_data /.

  Proposition disj_presheaf_predicate_law
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : psh_term_law (disj_presheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use sieve_eq.
    - intros y g.
      use factor_through_squash_hProp.
      intros [ q | q ].
      + use hdisj_in1.
        use (from_sieve_eq_l (psh_term_naturality φ f xx) g).
        exact q.
      + use hdisj_in2.
        use (from_sieve_eq_l (psh_term_naturality ψ f xx) g).
        exact q.
    - intros y g.
      use factor_through_squash_hProp.
      intros [ q | q ].
      + use hdisj_in1.
        use (from_sieve_eq_r (psh_term_naturality φ f xx) g).
        exact q.
      + use hdisj_in2.
        use (from_sieve_eq_r (psh_term_naturality ψ f xx) g).
        exact q.
  Qed.

  Definition disj_presheaf_predicate
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (disj_presheaf_predicate_data φ ψ).
    - exact (disj_presheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ∨ ψ" := (disj_presheaf_predicate φ ψ) : psh.

  Proposition disj_presheaf_intro_l
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : φ ⊢ φ ∨ ψ.
  Proof.
    intros x y f xx p.
    use hdisj_in1 ; cbn.
    exact p.
  Qed.

  Proposition disj_presheaf_intro_r
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : ψ ⊢ φ ∨ ψ.
  Proof.
    intros x y f xx p.
    use hdisj_in2 ; cbn.
    exact p.
  Qed.

  Proposition disj_presheaf_elim
              {Γ : C^op ⟶ HSET}
              {φ ψ χ : presheaf_predicate Γ}
              (p : φ ⊢ χ)
              (q : ψ ⊢ χ)
    : φ ∨ ψ ⊢ χ.
  Proof.
    intros x y f xx.
    use factor_through_squash_hProp ; cbn.
    intro r.
    induction r as [ r | r ].
    - exact (p x y f xx r).
    - exact (q x y f xx r).
  Qed.

  Proposition disj_presheaf_subst
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
              (φ ψ : presheaf_predicate Γ₂)
    : (φ ∨ ψ) [ s ] ⊢ φ [ s ] ∨ ψ [ s ].
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 7. Implication *)
  Definition impl_sieve
             {x : C}
             (ω₁ ω₂ : sieve x)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, ∀ (z : C) (g : z --> y), ω₁ z (g · f) ⇒ ω₂ z (g · f))%logic.
    - abstract
        (intros y₁ y₂ g₁ g₂ h p q z k r ; cbn ; cbn in q ;
         induction p ;
         rewrite assoc ;
         refine (q z (k · h) _) ;
         rewrite assoc' ;
         exact r).
  Defined.

  Definition impl_presheaf_predicate_data
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : psh_term_data (dep_psh_subobject_classifier_ob Γ)
    := λ x xx, impl_sieve (φ x xx) (ψ x xx).

  Proposition impl_presheaf_predicate_law
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : psh_term_law (impl_presheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use sieve_eq.
    - intros y g p z h q.
      cbn in g, h, q ; cbn.
      cbn in p.
      specialize (p z h).
      cbn in p.
      rewrite (psh_term_naturality φ) in p.
      rewrite (psh_term_naturality ψ) in p.
      cbn in p.
      rewrite assoc.
      apply p.
      rewrite assoc'.
      exact q.
    - intros y g p z h q.
      cbn in g, h, q ; cbn.
      rewrite (psh_term_naturality ψ) ; cbn.
      rewrite assoc'.
      cbn in p.
      apply (p z h).
      rewrite assoc.
      rewrite (psh_term_naturality φ) in q.
      exact q.
  Qed.

  Definition impl_presheaf_predicate
             {Γ : C^op ⟶ HSET}
             (φ ψ : presheaf_predicate Γ)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (impl_presheaf_predicate_data φ ψ).
    - exact (impl_presheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ⇒ ψ" := (impl_presheaf_predicate φ ψ) : psh.

  Proposition impl_presheaf_elim
              {Γ : C^op ⟶ HSET}
              (φ ψ : presheaf_predicate Γ)
    : φ ∧ (φ ⇒ ψ) ⊢ ψ.
  Proof.
    intros x₁ x₂ f xx [ p q ].
    cbn ; cbn in p, q.
    specialize (q x₂ (identity _)).
    rewrite !id_left in q.
    apply q.
    exact p.
  Qed.

  Proposition impl_presheaf_intro
              {Γ : C^op ⟶ HSET}
              {φ ψ χ : presheaf_predicate Γ}
              (p : conj_presheaf_predicate φ χ ⊢ ψ)
    : χ ⊢ (φ ⇒ ψ).
  Proof.
    intros x₁ x₂ f xx q z g r.
    specialize (p _ _ (g · f) xx).
    cbn in p, g, r ; cbn.
    apply p.
    split.
    - exact r.
    - exact (#ω (χ x₁ xx) g (idpath _) q).
  Qed.

  Proposition impl_presheaf_subst
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
              (φ ψ : presheaf_predicate Γ₂)
    : (φ [ s ]) ⇒ (ψ [ s ]) ⊢ (φ ⇒ ψ) [ s ].
  Proof.
    intros x₁ x₂ f xx p y g q.
    cbn in g, q ; cbn.
    apply (p y g).
    exact q.
  Qed.

  (** * 8. Universal quantification *)
  Definition forall_presheaf_sieve_ob
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
             {x y : C}
             (xx : (Γ x : hSet))
             (f : y --> x)
    : hProp
    := ∀ (z : C)
         (g : z --> y)
         (a : (A z : hSet)),
       (φ z (#Γ(g · f) xx ,, a) : sieve _) z (identity z).

  Proposition forall_presheaf_sieve_law
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
              {x y₁ y₂ : C}
              {xx : (Γ x : hSet)}
              (g₁ : y₁ --> x)
              (g₂ : y₂ --> x)
              (h : y₂ --> y₁)
              (p : h · g₁ = g₂)
              (q : forall_presheaf_sieve_ob φ xx g₁)
    : forall_presheaf_sieve_ob φ xx g₂.
  Proof.
    induction p.
    intros z g a.
    specialize (q z (g · h) a).
    cbn in q.
    rewrite assoc.
    exact q.
  Qed.

  Definition forall_presheaf_sieve
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
             {x : C}
             (xx : (Γ x : hSet))
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, forall_presheaf_sieve_ob φ xx f).
    - intros y₁ y₂ g₁ g₂ h p q.
      exact (forall_presheaf_sieve_law φ g₁ g₂ h p q).
  Defined.

  Definition forall_presheaf_predicate_data
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
    : psh_term_data (dep_psh_subobject_classifier_ob Γ)
    := λ x xx, forall_presheaf_sieve φ xx.

  Proposition forall_presheaf_predicate_law
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
    : psh_term_law (forall_presheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f xx.
    use sieve_eq.
    - cbn ; intros y g p z h b.
      specialize (p z h b).
      simple refine (from_sieve_eq_l (psh_term_on_eq φ _) _ _).
      + exact (#Γ (h · g) (#Γ f xx) ,, b).
      + apply maponpaths_2.
        refine (!(eqtohomot (functor_comp Γ _ _) _) @ _).
        cbn.
        rewrite assoc'.
        apply idpath.
      + cbn.
        rewrite id_left.
        exact p.
    - cbn ; intros y g p z h b.
      specialize (p z h b).
      simple refine (from_sieve_eq_l (psh_term_on_eq φ _) _ _).
      + exact (#Γ (h · (g · f)) xx ,, b).
      + apply maponpaths_2.
        refine (_ @ eqtohomot (functor_comp Γ _ _) _).
        cbn.
        rewrite assoc'.
        apply idpath.
      + cbn.
        rewrite id_left.
        exact p.
  Qed.

  Definition forall_presheaf_predicate
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (forall_presheaf_predicate_data φ).
    - exact (forall_presheaf_predicate_law φ).
  Defined.

  Local Notation "∀h φ" := (forall_presheaf_predicate φ) : psh.

  Proposition forall_presheaf_intro
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
    : (∀h φ) [ π₁ ] ⊢ φ.
  Proof.
    cbn.
    intros x₁ x₂ f [ xx a ] p.
    specialize (p x₂ (identity _) (#A f a)).
    cbn in p.
    rewrite id_left in p.
    pose (psh_term_naturality φ f (xx ,, a)) as q.
    cbn in q ; unfold prodtofuntoprod in q ; cbn in q.
    rewrite q in p.
    cbn in p.
    rewrite id_left in p.
    exact p.
  Qed.

  Proposition forall_presheaf_elim
              {Γ A : C^op ⟶ HSET}
              {φ : presheaf_predicate (Γ ×P A)}
              {ψ : presheaf_predicate Γ}
              (p : ψ[ π₁ ]  ⊢ φ)
    : (ψ ⊢ ∀h φ).
  Proof.
    intros x₁ x₂ f xx q y g a.
    use (p _ _ (identity y) (#Γ (g · f) xx ,, a)).
    cbn.
    pose (psh_term_naturality ψ (g · f) xx) as r.
    cbn in r.
    rewrite r.
    cbn.
    rewrite id_left.
    exact (#ω (ψ _ _) _ (idpath _) q).
  Qed.

  (** * 9. Existential quantification *)
  Definition exists_presheaf_sieve
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
             {x : C}
             (xx : (Γ x : hSet))
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, ∃ (a : (A y : hSet)), (φ y (#Γ f xx ,, a) : sieve _) y (identity _)).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p ;
         induction p ;
         use factor_through_squash_hProp ;
         intros [ a p ] ;
         use hinhpr ;
         refine (#A h a ,, _) ;
         pose (from_sieve_eq_r (psh_term_naturality φ h (#Γ g₁ xx ,, a)) (identity _)) as q ;
         specialize (q (#ω (φ _ _) h (id_right _ @ !(id_left _)) p)) ;
         cbn in q ; unfold prodtofuntoprod in q ; cbn in q ;
         simple refine (from_sieve_eq_l (psh_term_on_eq φ _) _ _) ;
         [ exact (# Γ h (# Γ g₁ xx),, # A h a)
         | apply maponpaths_2 ;
           exact (!eqtohomot (functor_comp Γ g₁ h) xx)
         | cbn ;
           rewrite id_left ;
           exact q ]).
  Defined.

  Definition exists_presheaf_predicate_data
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
    : psh_term_data (dep_psh_subobject_classifier_ob Γ)
    := λ x xx, exists_presheaf_sieve φ xx.

  Proposition exists_presheaf_predicate_law
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
    : psh_term_law (exists_presheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f xx.
    use sieve_eq.
    - cbn -[exists_presheaf_sieve].
      intros y g.
      use factor_through_squash_hProp.
      intros [ a p ] ; cbn in a, p.
      use hinhpr ; cbn.
      refine (a ,, _).
      simple refine (from_sieve_eq_l (psh_term_on_eq φ _) _ _).
      + exact (#Γ g (#Γ f xx) ,, a).
      + apply maponpaths_2.
        exact (!(eqtohomot (functor_comp Γ _ _) xx)).
      + cbn.
        rewrite id_left.
        exact p.
    - cbn -[exists_presheaf_sieve].
      intros y g.
      use factor_through_squash_hProp.
      intros [ a p ] ; cbn in a, p.
      use hinhpr ; cbn.
      refine (a ,, _).
      simple refine (from_sieve_eq_l (psh_term_on_eq φ _) _ _).
      + exact (#Γ (g · f) xx ,, a).
      + apply maponpaths_2.
        exact (eqtohomot (functor_comp Γ _ _) xx).
      + cbn.
        rewrite id_left.
        exact p.
  Qed.

  Definition exists_presheaf_predicate
             {Γ A : C^op ⟶ HSET}
             (φ : presheaf_predicate (Γ ×P A))
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (exists_presheaf_predicate_data φ).
    - exact (exists_presheaf_predicate_law φ).
  Defined.

  Local Notation "∃h φ" := (exists_presheaf_predicate φ) : psh.

  Proposition exists_presheaf_intro
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
    : φ ⊢ (∃h φ) [ π₁ ].
  Proof.
    cbn -[exists_presheaf_sieve].
    intros x₁ x₂ f [ xx a ] p.
    use hinhpr.
    cbn.
    refine (#A f a ,, _).
    use (from_sieve_eq_r (psh_term_naturality φ f (xx ,, a)) (identity _)).
    cbn ; unfold prodtofuntoprod ; cbn.
    rewrite id_left.
    exact p.
  Qed.

  Proposition exists_presheaf_elim
              {Γ A : C^op ⟶ HSET}
              {φ : presheaf_predicate (Γ ×P A)}
              {ψ : presheaf_predicate Γ}
              (p : φ ⊢ ψ [ π₁ ])
    : (∃h φ ⊢ ψ).
  Proof.
    cbn -[exists_presheaf_sieve].
    intros x₁ x₂ f xx.
    use factor_through_squash_hProp.
    intros [ a q ].
    cbn in a, q.
    specialize (p _ _ (identity x₂) (#Γ f xx ,, a) q).
    cbn in p.
    pose (from_sieve_eq_l (psh_term_naturality ψ f xx) (identity _) p) as r.
    cbn in r.
    rewrite id_left in r.
    exact r.
  Qed.

  Local Close Scope psh.

  (** * 10. Equality *)
  Definition eq_presheaf_predicate_sieve
             {Γ : C^op ⟶ HSET}
             (φ : presheaf_predicate Γ)
             {x : C}
             (xx yy : (Γ x : hSet))
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, ((φ x xx : sieve _) y f ∧ #Γ f xx = #Γ f yy)%logic).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p q ;
         cbn in q ;
         induction p ;
         cbn ;
         refine (#ω (φ x xx) _ (idpath _) (pr1 q) ,, _) ;
         refine (eqtohomot (functor_comp Γ _ _) _ @ _) ;
         refine (_ @ !(eqtohomot (functor_comp Γ _ _) _)) ;
         cbn ;
         apply maponpaths ;
         apply q ;
         exact r).
  Defined.

  Local Open Scope psh.

  Definition eq_presheaf_predicate_data
             {Γ : C^op ⟶ HSET}
             (φ : presheaf_predicate Γ)
    : psh_term_data (dep_psh_subobject_classifier_ob (Γ ×P Γ))
    := λ x xx, eq_presheaf_predicate_sieve φ (pr1 xx) (pr2 xx).

  Arguments eq_presheaf_predicate_data /.

  Proposition eq_presheaf_predicate_law
              {Γ : C^op ⟶ HSET}
              (φ : presheaf_predicate Γ)
    : psh_term_law (eq_presheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f [ xx₁ xx₂ ].
    use sieve_eq ; cbn.
    - intros y g [ p q ].
      split.
      + pose (psh_term_naturality φ f xx₁) as r.
        cbn in r.
        rewrite r in p.
        cbn in p.
        exact p.
      + refine (eqtohomot (functor_comp Γ _ _) _ @ _).
        refine (_ @ !(eqtohomot (functor_comp Γ _ _) _)).
        cbn.
        apply q.
    - intros y g [ p q ].
      split.
      + pose (psh_term_naturality φ f xx₁) as r.
        cbn in r.
        rewrite r.
        exact p.
      + refine (!(eqtohomot (functor_comp Γ _ _) _) @ _).
        refine (_ @ eqtohomot (functor_comp Γ _ _) _).
        cbn.
        exact q.
  Qed.

  Definition eq_presheaf_predicate
             {Γ : C^op ⟶ HSET}
             (φ : presheaf_predicate Γ)
    : presheaf_predicate (Γ ×P Γ).
  Proof.
    use make_psh_term.
    - exact (eq_presheaf_predicate_data φ).
    - exact (eq_presheaf_predicate_law φ).
  Defined.

  Proposition eq_presheaf_intro
              {Γ : C^op ⟶ HSET}
              (φ : presheaf_predicate Γ)
    : φ ⊢ (eq_presheaf_predicate φ) [ ⟨ nat_trans_id _ , nat_trans_id _ ⟩ ].
  Proof.
    intros x y f xx p ; cbn.
    refine (p ,, _).
    apply idpath.
  Qed.

  Proposition eq_presheaf_elim
              {Γ : C^op ⟶ HSET}
              {φ : presheaf_predicate Γ}
              {ψ : presheaf_predicate (Γ ×P Γ)}
              (p : φ ⊢ ψ [ ⟨ nat_trans_id _ , nat_trans_id _ ⟩ ])
    : (eq_presheaf_predicate φ) ⊢ ψ.
  Proof.
    cbn ;  intros x y f xx [ q₁ q₂ ].
    specialize (p _ _ _ _ q₁).
    cbn in p.
    pose (from_sieve_eq_l (psh_term_naturality ψ f xx) (identity _)) as r.
    cbn in r ; unfold prodtofuntoprod in r ; cbn in r.
    refine (#ω (ψ x xx) (identity _) (id_left _ @ id_left _) (r _)).
    clear r.
    rewrite <- q₂.
    apply (from_sieve_eq_r (psh_term_naturality ψ f (pr1 xx ,, pr1 xx)) (identity _)).
    cbn.
    refine (#ω (ψ _ _) _ (idpath _) p).
  Qed.

  Definition equality_presheaf_predicate
             {Γ A : C^op ⟶ HSET}
             (τ₁ τ₂ : Γ ⟹ A)
    : presheaf_predicate Γ
    := psh_term_subst
         (binproduct_nat_trans _ _ _ _ _ _ τ₁ τ₂)
         (eq_presheaf_predicate (truth_presheaf_predicate A)).

  Local Notation "τ₁ ≡ τ₂" := (equality_presheaf_predicate τ₁ τ₂) : psh.

  (** * 11. The forcing relation *)
  Definition presheaf_forces
             {Γ : C^op ⟶ HSET}
             (x : C)
             (xx : (Γ x : hSet))
             (φ : presheaf_predicate Γ)
    : hProp
    := (φ x xx : sieve x) x (identity _).

  Notation "x ⊩_{ xx } φ" := (presheaf_forces x xx φ) (at level 100) : psh.

  (** * 12. Properties of the forcing relation *)
  Proposition presheaf_forces_monotone
              {Γ : C^op ⟶ HSET}
              {x y : C}
              (g : y --> x)
              {xx : (Γ x : hSet)}
              {φ : presheaf_predicate Γ}
              (p : x ⊩_{xx} φ)
    : y ⊩_{#Γ g xx} φ.
  Proof.
    unfold presheaf_forces in *.
    apply (from_sieve_eq_r (psh_term_naturality φ g xx) (identity y)).
    cbn.
    refine (#ω (φ x xx) g _ p).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition forces_truth_presheaves
              {Γ : C^op ⟶ HSET}
              (x : C)
              (xx : (Γ x : hSet))
    : x ⊩_{xx} ⊤.
  Proof.
    cbn.
    exact tt.
  Qed.

  Proposition forces_false_presheaves
              {Γ : C^op ⟶ HSET}
              (x : C)
              (xx : (Γ x : hSet))
    : ¬(x ⊩_{xx} ⊥).
  Proof.
    cbn.
    intro z.
    induction z.
  Qed.

  Proposition forces_and_presheaves
              {Γ : C^op ⟶ HSET}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : presheaf_predicate Γ)
    : (x ⊩_{xx} φ ∧ ψ)%psh ≃ ((x ⊩_{xx} φ) × (x ⊩_{xx} ψ)).
  Proof.
    exact (idweq _).
  Qed.

  Proposition forces_or_presheaves
              {Γ : C^op ⟶ HSET}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : presheaf_predicate Γ)
    : (x ⊩_{xx} φ ∨ ψ)%psh ≃ ((x ⊩_{xx} φ) ∨ (x ⊩_{xx} ψ)).
  Proof.
    exact (idweq _).
  Qed.

  Proposition forces_impl_presheaves
              {Γ : C^op ⟶ HSET}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : presheaf_predicate Γ)
    : (x ⊩_{xx} φ ⇒ ψ)
      ≃
      (∀ (y : C) (g : y --> x), (y ⊩_{#Γ g xx} φ) ⇒ (y ⊩_{#Γ g xx} ψ))%logic.
  Proof.
    use logeqweq.
    - cbn.
      intros H y f p.
      specialize (H y f).
      unfold presheaf_forces in *.
      apply (from_sieve_eq_r (psh_term_naturality ψ f xx)).
      cbn.
      rewrite id_left.
      rewrite !id_right in H.
      apply H.
      pose (from_sieve_eq_l (psh_term_naturality φ f xx) _ p) as q.
      cbn in q.
      rewrite id_left in q.
      exact q.
    - cbn.
      intros H y f p.
      specialize (H y f).
      unfold presheaf_forces in H.
      pose (from_sieve_eq_l (psh_term_naturality ψ f xx) (identity _)) as q.
      cbn in q.
      rewrite id_left in q.
      rewrite id_right.
      apply q.
      apply H.
      apply (from_sieve_eq_r (psh_term_naturality φ f xx)).
      cbn.
      rewrite id_left.
      rewrite id_right in p.
      exact p.
  Qed.

  Proposition forces_equality_presheaves
              {Γ A : C^op ⟶ HSET}
              (τ₁ τ₂ : Γ ⟹ A)
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} τ₁ ≡ τ₂)
      ≃
      (τ₁ x xx = τ₂ x xx)%logic.
  Proof.
    use logeqweq.
    - cbn.
      intros [ _ p ].
      exact (!(eqtohomot (functor_id A _) _) @ p @ eqtohomot (functor_id A _) _).
    - cbn.
      intro p.
      induction p.
      exact (tt ,, idpath _).
  Qed.

  Proposition forces_forall_presheaves
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} ∀h φ)
      ≃
      (∀ (y : C) (g : y --> x) (a : (A y : hSet)),
       y ⊩_{((#Γ g xx ,, a) : (Γ ×P A) y : hSet)} φ).
  Proof.
    use logeqweq.
    - cbn.
      intros H y g a.
      unfold presheaf_forces.
      specialize (H y g a).
      rewrite id_right in H.
      exact H.
    - cbn.
      intros H y g a.
      unfold presheaf_forces.
      specialize (H y g a).
      rewrite id_right.
      exact H.
  Qed.

  Proposition forces_exists_presheaves
              {Γ A : C^op ⟶ HSET}
              (φ : presheaf_predicate (Γ ×P A))
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} ∃h φ)
      ≃
      (∃ (a : (A x : hSet)), x ⊩_{((xx ,, a) : (Γ ×P A) x : hSet)} φ).
  Proof.
    use logeqweq.
    - use factor_through_squash_hProp.
      intros [ a p ].
      use hinhpr.
      cbn in a, p ; cbn.
      refine (a ,, _).
      cbn.
      assert ((#Γ (identity x) xx,, a) = (xx ,, a)) as q.
      {
        apply maponpaths_2.
        exact (eqtohomot (functor_id Γ _) xx).
      }
      pose (from_sieve_eq_l (psh_term_pt_eq φ q) (identity x) p) as h.
      cbn in h.
      rewrite id_left in h.
      exact h.
    - use factor_through_squash_hProp.
      intros [ a p ].
      use hinhpr.
      cbn in a, p ; cbn.
      refine (a ,, _).
      cbn.
      assert ((#Γ (identity x) xx,, a) = (xx ,, a)) as q.
      {
        apply maponpaths_2.
        exact (eqtohomot (functor_id Γ _) xx).
      }
      apply (from_sieve_eq_r (psh_term_pt_eq φ q) (identity x)).
      cbn.
      rewrite id_left.
      exact p.
  Qed.

  Proposition forces_entailment_presheaves
              {Γ : C^op ⟶ HSET}
              (φ : presheaf_predicate Γ)
    : (⊤ ⊢ φ)
      ≃
      ∀ (x : C) (xx : (Γ x : hSet)), x ⊩_{xx} φ.
  Proof.
    use logeqweq.
    - cbn.
      intros H x y.
      apply H.
      exact tt.
    - intros H x y f xx _.
      specialize (H x xx) ; cbn in H.
      refine (#ω (φ x xx) f _ H).
      apply id_right.
  Qed.
End PresheafLogic.

Notation "x ⊩_{ xx } φ" := (presheaf_forces x xx φ) (at level 100) : psh.
