(**

 Logic in the sheaf model

 Both presheaves and sheaves form a topos, and hence they give rise to a model of
 higher-order logic. One nice feature of their higher-order logic is that we can
 give simplified and concrete descriptions of their connectives, and that we can
 use Kripke-Joyal semantics to check the validity of a formula by checking whether
 it holds at each of the stages (i.e., objects of the site).

 There is a key difference between the logic of sheaves and of presheaves. Several
 connectives, namely `⊤`, `∧`, `⇒`, `∀`, `≡`, are interpreted the same for sheaves
 and for presheaves, but some of them, namely `⊥`, `∨`, and `∃`, are different. This
 difference is similar to how limits and colimits are constructed in sheaf categories:
 while finite limits of sheaves are calculated as finite limits of presheaves, this
 is not so for finite colimits. Finite colimits of sheaves are sheafifications of finite
 colimits of presheaves. Concretely, the initial sheaf is the sheafification of the initial
 presheaf. While the connectives `⊤`, `∧`, `⇒`, `∀`, `≡` are calculated for sheaves the
 same way as for presheaves, we need to take a closure of sieves to describe `⊥`, `∨`,
 and `∃`. For this reason, these connectives have a more complicated description in the
 sheaf model compared to the presheaf model.

 Content
 1. Preliminary operations
 2. Predicates and entailment in the sheaf model
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
Require Import UniMath.CategoryTheory.Presheaves.PresheafLogic.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.

Local Open Scope cat.

Declare Scope sh.
Delimit Scope sh with sh.

(** * 1. Preliminary operations *)
Definition sheaf_product
           {C : site}
           (Γ₁ Γ₂ : sheaf C)
  : sheaf C.
Proof.
  use make_sheaf.
  - exact (BinProduct_of_functors C^op SET BinProductsHSET Γ₁ Γ₂).
  - apply is_sheaf_binproduct ; apply is_sheaf_sheaf.
Defined.

Notation "Γ₁ ×P Γ₂" := (sheaf_product Γ₁ Γ₂) (at level 75) : sh.

Definition pr1_sheaf
           {C : site}
           (Γ₁ Γ₂ : sheaf C)
  : sheaf_nat_trans (Γ₁ ×P Γ₂)%sh Γ₁.
Proof.
  use make_sheaf_nat_trans.
  exact (binproduct_nat_trans_pr1 _ _ _ _ _).
Defined.

Definition pr2_sheaf
           {C : site}
           (Γ₁ Γ₂ : sheaf C)
  : sheaf_nat_trans (Γ₁ ×P Γ₂)%sh Γ₂.
Proof.
  use make_sheaf_nat_trans.
  exact (binproduct_nat_trans_pr2 _ _ _ _ _).
Defined.

Notation "'π₁'" := (pr1_sheaf _ _) : sh.
Notation "'π₂'" := (pr2_sheaf _ _) : sh.

Definition pair_sheaf
           {C : site}
           {Γ Δ₁ Δ₂ : sheaf C}
           (τ₁ : Γ ⟹ Δ₁)
           (τ₂ : Γ ⟹ Δ₂)
  : sheaf_nat_trans Γ (Δ₁ ×P Δ₂)%sh.
Proof.
  use make_sheaf_nat_trans.
  exact (binproduct_nat_trans _ _ _ _ _ _ τ₁ τ₂).
Defined.

Notation "⟨ τ₁ , τ₂ ⟩" := (pair_sheaf τ₁ τ₂) : sh.

Definition sheaf_binproducts
           (C : site)
  : BinProducts (cat_of_sheaves C).
Proof.
  refine (λ (Γ₁ Γ₂ : sheaf C), _).
  use make_BinProduct.
  - exact (Γ₁ ×P Γ₂)%sh.
  - exact π₁%sh.
  - exact π₂%sh.
  - refine (λ (Δ : sheaf C) (τ₁ : sheaf_nat_trans Δ Γ₁) (τ₂ : sheaf_nat_trans Δ Γ₂), _).
    use make_iscontr.
    + simple refine (_ ,, _ ,, _).
      * exact ⟨ τ₁ , τ₂ ⟩%sh.
      * abstract
          (use sheaf_nat_trans_eq ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro ;
           apply idpath).
      * abstract
          (use sheaf_nat_trans_eq ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro ;
           apply idpath).
    + abstract
        (intros θpq ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use sheaf_nat_trans_eq ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ;
         cbn ; unfold prodtofuntoprod ; cbn ;
         use funextsec ;
         intro xx ;
         exact (pathsdirprod
                  (maponpaths (λ z, pr11 z x xx) (pr12 θpq))
                  (maponpaths (λ z, pr11 z x xx) (pr22 θpq)))).
Defined.

Section SheafLogic.
  Context {C : site}.

  Local Open Scope sh.

  (** * 2. Predicates and entailment in the sheaf model *)
  Definition sheaf_predicate
             (Γ : sheaf C)
    : UU
    := psh_term (subobject_classifier_dep_sheaf Γ).

  Identity Coercion sheaf_predicate_to_term : sheaf_predicate >-> psh_term.

  Definition sheaf_predicate_to_presheaf_predicate
             {Γ : sheaf C}
             (φ : sheaf_predicate Γ)
    : presheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (λ x xx, ((φ x xx : closed_sieve x) : sieve x)).
    - abstract
        (intros x y f xx ; cbn ;
         exact (sieve_eq_from_closed (psh_term_naturality φ f xx))).
  Defined.

  Definition sheaf_predicate_subst
             {Γ₁ Γ₂ : sheaf C}
             (s : sheaf_nat_trans Γ₁ Γ₂)
             (φ : sheaf_predicate Γ₂)
    : sheaf_predicate Γ₁
    := psh_term_subst s φ.

  Local Notation "φ [ s ]" := (sheaf_predicate_subst s φ) : sh.

  Definition sheaf_predicate_entails
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : UU
    := ∀ (x y : C)
         (f : y --> x)
         (xx : (Γ x : hSet)),
       ((φ x xx : closed_sieve x) y f ⇒ (ψ x xx : closed_sieve x) y f)%logic.

  Local Notation "φ ⊢ ψ" := (sheaf_predicate_entails φ ψ) : sh.

  (** * 3. The truth formula *)
  Definition truth_sheaf_predicate
             (Γ : sheaf C)
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (λ x xx, truth_closed_sieve x).
    - abstract
        (intros x₁ x₂ f xx ; cbn ;
         use closed_sieve_eq ;
         use sieve_eq ;
         intros ;
         exact tt).
  Defined.

  Local Notation "⊤" := (truth_sheaf_predicate _) : sh.

  Proposition truth_sheaf_intro
              {Γ : sheaf C}
              (φ : sheaf_predicate Γ)
    : φ ⊢ ⊤.
  Proof.
    intros x y f xx p ; cbn.
    exact tt.
  Qed.

  Proposition truth_sheaf_subst
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
    : ⊤ ⊢ ⊤ [ s ].
  Proof.
    intros x y f xx _.
    exact tt.
  Qed.

  (** * 4. The falsity formula *)
  Definition false_closed_sieve
             (x : C)
    : closed_sieve x.
  Proof.
    use closure_closed_sieve.
    exact (false_sieve x).
  Defined.

  Definition false_sheaf_predicate_data
             (Γ : sheaf C)
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, false_closed_sieve x.

  Proposition false_sheaf_predicate_laws
              (Γ : sheaf C)
    : psh_term_law (false_sheaf_predicate_data Γ).
  Proof.
    intros x₁ x₂ f xx ; cbn.
    use closed_sieve_eq.
    use sieve_eq ; intros ? ? p.
    - unfold false_closed_sieve.
      cbn -[precomp_sieve].
      rewrite precomp_closure_sieve.
      use (closure_monotone _ _ p).
      clear y g p.
      cbn.
      intros y g z.
      exact z.
    - unfold false_closed_sieve.
      cbn -[precomp_sieve closure_sieve] in p.
      rewrite precomp_closure_sieve in p.
      cbn -[closure_sieve].
      use (closure_monotone _ _ p).
      clear y g p.
      intros y g z.
      exact z.
  Qed.

  Definition false_sheaf_predicate
             (Γ : sheaf C)
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (false_sheaf_predicate_data Γ).
    - exact (false_sheaf_predicate_laws Γ).
  Defined.

  Local Notation "⊥" := (false_sheaf_predicate _) : sh.

  Proposition false_sheaf_elim
              {Γ : sheaf C}
              (φ : sheaf_predicate Γ)
    : ⊥ ⊢ φ.
  Proof.
    cbn -[closure_sieve].
    intros x y f xx.
    use contains_closure_sieve.
    clear y f.
    intros y f.
    cbn.
    exact (false_presheaf_elim (sheaf_predicate_to_presheaf_predicate φ) x y f xx).
  Qed.

  Proposition false_sheaf_subst
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
    : ⊥ [ s ] ⊢ ⊥.
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 5. Conjunction *)
  Proposition is_closed_conj_sieve
              {x : C}
              (ω₁ ω₂ : closed_sieve x)
    : is_closed_sieve (conj_sieve ω₁ ω₂).
  Proof.
    intros y g p.
    split ; cbn.
    - refine (closed_sieve_closed ω₁ g _).
      use (site_trans_sieve p).
      cbn ; intros z h q.
      rewrite <- comp_precomp_sieve.
      use sieve_contains_closed.
      exact (pr1 q).
    - refine (closed_sieve_closed ω₂ g _).
      use (site_trans_sieve p).
      cbn ; intros z h q.
      rewrite <- comp_precomp_sieve.
      use sieve_contains_closed.
      exact (pr2 q).
  Qed.

  Definition conj_closed_sieve
             {x : C}
             (ω₁ ω₂ : closed_sieve x)
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (conj_sieve ω₁ ω₂).
    - exact (is_closed_conj_sieve ω₁ ω₂).
  Defined.

  Definition conj_sheaf_predicate_data
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, conj_closed_sieve (φ x xx) (ψ x xx).

  Arguments conj_presheaf_predicate_data /.

  Proposition conj_sheaf_predicate_law
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : psh_term_law (conj_sheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    use sieve_eq ; cbn.
    - intros y g [ p₁ p₂ ].
      split.
      + use (from_sieve_eq_l (sieve_eq_from_closed (psh_term_naturality φ f xx)) g).
        exact p₁.
      + use (from_sieve_eq_l (sieve_eq_from_closed (psh_term_naturality ψ f xx)) g).
        exact p₂.
    - intros y g [ p₁ p₂ ].
      split.
      + use (from_sieve_eq_r (sieve_eq_from_closed (psh_term_naturality φ f xx)) g).
        exact p₁.
      + use (from_sieve_eq_r (sieve_eq_from_closed (psh_term_naturality ψ f xx)) g).
        exact p₂.
  Qed.

  Definition conj_sheaf_predicate
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (conj_sheaf_predicate_data φ ψ).
    - exact (conj_sheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ∧ ψ" := (conj_sheaf_predicate φ ψ) : sh.

  Proposition conj_sheaf_intro
              {Γ : sheaf C}
              {φ ψ χ : sheaf_predicate Γ}
              (p : χ ⊢ φ)
              (q : χ ⊢ ψ)
    : χ ⊢ φ ∧ ψ.
  Proof.
    intros x y f xx r ; cbn.
    exact (p x y f xx r ,, q x y f xx r).
  Qed.

  Proposition conj_sheaf_elim_l
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : φ ∧ ψ ⊢ φ.
  Proof.
    intros x y f xx r ; cbn in r.
    exact (pr1 r).
  Qed.

  Proposition conj_sheaf_elim_r
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : φ ∧ ψ ⊢ ψ.
  Proof.
    intros x y f xx r ; cbn in r.
    exact (pr2 r).
  Qed.

  Proposition conj_sheaf_subst
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              (φ ψ : sheaf_predicate Γ₂)
    : φ [ s ] ∧ ψ [ s ] ⊢ (φ ∧ ψ) [ s ].
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 6. Disjunction *)
  Definition disj_closed_sieve
             {x : C}
             (ω₁ ω₂ : closed_sieve x)
    : closed_sieve x
    := closure_closed_sieve (disj_sieve ω₁ ω₂).

  Definition disj_sheaf_predicate_data
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, disj_closed_sieve (φ x xx) (ψ x xx).

  Arguments disj_sheaf_predicate_data /.

  Proposition disj_sheaf_predicate_law
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : psh_term_law (disj_sheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    use sieve_eq.
    - cbn -[closure_sieve] ; intros y g.
      pose (psh_term_naturality
              (disj_presheaf_predicate
                 (sheaf_predicate_to_presheaf_predicate φ)
                 (sheaf_predicate_to_presheaf_predicate ψ))
              f
              xx)
        as p.
      cbn in p.
      unfold disj_presheaf_predicate_data in p.
      cbn in p.
      rewrite p.
      rewrite <- (precomp_closure_sieve _ f).
      cbn -[closure_sieve].
      exact (λ z, z).
    - cbn -[closure_sieve] ; intros y g.
      pose (psh_term_naturality
              (disj_presheaf_predicate
                 (sheaf_predicate_to_presheaf_predicate φ)
                 (sheaf_predicate_to_presheaf_predicate ψ))
              f
              xx)
        as p.
      cbn in p.
      unfold disj_presheaf_predicate_data in p.
      cbn in p.
      rewrite p.
      rewrite <- (precomp_closure_sieve _ f).
      cbn -[closure_sieve].
      exact (λ z, z).
  Qed.

  Definition disj_sheaf_predicate
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (disj_sheaf_predicate_data φ ψ).
    - exact (disj_sheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ∨ ψ" := (disj_sheaf_predicate φ ψ) : sh.

  Proposition disj_sheaf_intro_l
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : φ ⊢ φ ∨ ψ.
  Proof.
    intros x y f xx p.
    use closure_sieve_contains.
    exact (disj_presheaf_intro_l
             (sheaf_predicate_to_presheaf_predicate φ)
             (sheaf_predicate_to_presheaf_predicate ψ)
             x y
             f
             xx
             p).
  Qed.

  Proposition disj_sheaf_intro_r
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : ψ ⊢ φ ∨ ψ.
  Proof.
    intros x y f xx p.
    use closure_sieve_contains.
    exact (disj_presheaf_intro_r
             (sheaf_predicate_to_presheaf_predicate φ)
             (sheaf_predicate_to_presheaf_predicate ψ)
             x y
             f
             xx
             p).
  Qed.

  Proposition disj_sheaf_elim
              {Γ : sheaf C}
              {φ ψ χ : sheaf_predicate Γ}
              (p : φ ⊢ χ)
              (q : ψ ⊢ χ)
    : φ ∨ ψ ⊢ χ.
  Proof.
    intros x y f xx.
    use contains_closure_sieve.
    clear y f.
    intros y f.
    use (disj_presheaf_elim
           (φ := sheaf_predicate_to_presheaf_predicate φ)
           (ψ := sheaf_predicate_to_presheaf_predicate ψ)
           (χ  := sheaf_predicate_to_presheaf_predicate χ)).
    - exact p.
    - exact q.
  Qed.

  Proposition disj_sheaf_subst
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              (φ ψ : sheaf_predicate Γ₂)
    : (φ ∨ ψ) [ s ] ⊢ φ [ s ] ∨ ψ [ s ].
  Proof.
    intros x y f xx p.
    cbn in p ; cbn.
    exact p.
  Qed.

  (** * 7. Implication *)
  Proposition is_closed_impl_sieve
              {x : C}
              (ω₁ ω₂ : closed_sieve x)
    : is_closed_sieve (impl_sieve ω₁ ω₂).
  Proof.
    intros y f p z g q.
    cbn in *.
    use closed_sieve_closed.
    rewrite comp_precomp_sieve.
    apply sieve_contains_closed in q.
    pose (site_sieve_stable g p) as h.
    use (site_trans_sieve h).
    cbn ; clear h.
    intros w h H.
    apply sieve_contains_closed.
    specialize (H w (identity _)).
    rewrite !id_left in H.
    cbn.
    apply H.
    use (closed_sieve_closed ω₁).
    rewrite !comp_precomp_sieve.
    use site_sieve_stable.
    rewrite comp_precomp_sieve in q.
    exact q.
  Qed.

  Definition impl_closed_sieve
             {x : C}
             (ω₁ ω₂ : closed_sieve x)
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (impl_sieve ω₁ ω₂).
    - apply is_closed_impl_sieve.
  Defined.

  Definition impl_sheaf_predicate_data
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, impl_closed_sieve (φ x xx) (ψ x xx).

  Proposition impl_sheaf_predicate_law
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : psh_term_law (impl_sheaf_predicate_data φ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    exact (impl_presheaf_predicate_law
             (sheaf_predicate_to_presheaf_predicate φ)
             (sheaf_predicate_to_presheaf_predicate ψ)
             x₁ x₂
             f
             xx).
  Qed.

  Definition impl_sheaf_predicate
             {Γ : sheaf C}
             (φ ψ : sheaf_predicate Γ)
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (impl_sheaf_predicate_data φ ψ).
    - exact (impl_sheaf_predicate_law φ ψ).
  Defined.

  Local Notation "φ ⇒ ψ" := (impl_sheaf_predicate φ ψ) : sh.

  Proposition impl_sheaf_elim
              {Γ : sheaf C}
              (φ ψ : sheaf_predicate Γ)
    : φ ∧ (φ ⇒ ψ) ⊢ ψ.
  Proof.
    intros x₁ x₂ f xx [ p q ].
    cbn ; cbn in p, q.
    specialize (q x₂ (identity _)).
    rewrite !id_left in q.
    apply q.
    exact p.
  Qed.

  Proposition impl_sheaf_intro
              {Γ : sheaf C}
              {φ ψ χ : sheaf_predicate Γ}
              (p : conj_sheaf_predicate φ χ ⊢ ψ)
    : χ ⊢ (φ ⇒ ψ).
  Proof.
    intros x₁ x₂ f xx q z g r.
    specialize (p _ _ (g · f) xx).
    cbn in p, g, r ; cbn.
    apply p.
    split.
    - exact r.
    - exact (#ω (χ x₁ xx : closed_sieve _) g (idpath _) q).
  Qed.

  Proposition impl_sheaf_subst
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              (φ ψ : sheaf_predicate Γ₂)
    : (φ [ s ]) ⇒ (ψ [ s ]) ⊢ (φ ⇒ ψ) [ s ].
  Proof.
    intros x₁ x₂ f xx p y g q.
    cbn in g, q ; cbn.
    apply (p y g).
    exact q.
  Qed.

  (** * 8. Universal quantification *)
  Proposition is_closed_forall_sheaf_sieve
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
              {x : C}
              (xx : (Γ x : hSet))
    : is_closed_sieve
        (forall_presheaf_sieve
           (sheaf_predicate_to_presheaf_predicate φ)
           xx).
  Proof.
    cbn ; intros y f p z g a.
    use closed_sieve_closed.
    rewrite id_precomp_sieve.
    use (site_trans_sieve (site_sieve_stable g p)) ; cbn.
    intros w h H.
    specialize (H w (identity _) (#A h a)).
    rewrite id_left in H.
    use sieve_contains_closed.
    pose (from_sieve_eq_l
            (sieve_eq_from_closed (psh_term_naturality φ h (#Γ (g · f) xx ,, a)))
            (identity _))
      as q.
    cbn in q ; unfold prodtofuntoprod in q ; cbn in q.
    rewrite id_left in q.
    apply q.
    use (from_sieve_eq_l _ _ H).
    do 2 apply maponpaths.
    apply maponpaths_2.
    refine (_ @ eqtohomot (functor_comp Γ (g · f) h) xx).
    cbn.
    rewrite assoc.
    apply idpath.
  Qed.

  Definition forall_sheaf_closed_sieve
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
             {x : C}
             (xx : (Γ x : hSet))
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (forall_presheaf_sieve (sheaf_predicate_to_presheaf_predicate φ) xx).
    - exact (is_closed_forall_sheaf_sieve φ xx).
  Defined.

  Definition forall_sheaf_predicate_data
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, forall_sheaf_closed_sieve φ xx.

  Proposition forall_sheaf_predicate_law
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
    : psh_term_law (forall_sheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    exact (forall_presheaf_predicate_law
             (sheaf_predicate_to_presheaf_predicate φ)
             x₁ x₂
             f
             xx).
  Qed.

  Definition forall_sheaf_predicate
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (forall_sheaf_predicate_data φ).
    - exact (forall_sheaf_predicate_law φ).
  Defined.

  Local Notation "∀h φ" := (forall_sheaf_predicate φ) : sh.

  Proposition forall_sheaf_intro
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
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

  Proposition forall_sheaf_elim
              {Γ A : sheaf C}
              {φ : sheaf_predicate (Γ ×P A)}
              {ψ : sheaf_predicate Γ}
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
    exact (#ω (ψ _ _ : closed_sieve _) _ (idpath _) q).
  Qed.

  (** * 9. Existential quantification *)
  Definition exists_sheaf_closed_sieve
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
             {x : C}
             (xx : (Γ x : hSet))
    : closed_sieve x.
  Proof.
    use closure_closed_sieve.
    exact (exists_presheaf_sieve (sheaf_predicate_to_presheaf_predicate φ) xx).
  Defined.

  Definition exists_sheaf_predicate_data
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
    : psh_term_data (subobject_classifier_dep_sheaf Γ)
    := λ x xx, exists_sheaf_closed_sieve φ xx.

  Proposition exists_sheaf_predicate_law
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
    : psh_term_law (exists_sheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    use sieve_eq.
    - cbn -[closure_sieve] ; intros y g.
      pose (psh_term_naturality
              (exists_presheaf_predicate (sheaf_predicate_to_presheaf_predicate φ))
              f
              xx)
        as p.
      cbn in p.
      unfold exists_presheaf_predicate_data in p.
      cbn in p.
      rewrite p.
      rewrite <- (precomp_closure_sieve _ f).
      cbn -[closure_sieve].
      exact (λ z, z).
    - cbn -[closure_sieve] ; intros y g.
      pose (psh_term_naturality
              (exists_presheaf_predicate (sheaf_predicate_to_presheaf_predicate φ))
              f
              xx)
        as p.
      cbn in p.
      unfold exists_presheaf_predicate_data in p.
      cbn in p.
      rewrite p.
      rewrite <- (precomp_closure_sieve _ f).
      cbn -[closure_sieve].
      exact (λ z, z).
  Qed.

  Definition exists_sheaf_predicate
             {Γ A : sheaf C}
             (φ : sheaf_predicate (Γ ×P A))
    : sheaf_predicate Γ.
  Proof.
    use make_psh_term.
    - exact (exists_sheaf_predicate_data φ).
    - exact (exists_sheaf_predicate_law φ).
  Defined.

  Local Notation "∃h φ" := (exists_sheaf_predicate φ) : sh.

  Proposition exists_sheaf_intro
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
    : φ ⊢ (∃h φ) [ π₁ ].
  Proof.
    intros x₁ x₂ f [ xx a ] p.
    use closure_sieve_contains.
    exact (exists_presheaf_intro
             (sheaf_predicate_to_presheaf_predicate φ)
             _ _ _ _
             p).
  Qed.

  Proposition exists_sheaf_elim
              {Γ A : sheaf C}
              {φ : sheaf_predicate (Γ ×P A)}
              {ψ : sheaf_predicate Γ}
              (p : φ ⊢ ψ [ π₁ ])
    : (∃h φ ⊢ ψ).
  Proof.
    intros x₁ x₂ f xx.
    use contains_closure_sieve.
    intros y g q.
    exact (exists_presheaf_elim
             (φ := sheaf_predicate_to_presheaf_predicate φ)
             (ψ := sheaf_predicate_to_presheaf_predicate ψ)
             p
             _ _ _ _
             q).
  Qed.

  Proposition exists_sheaf_subst
              {Γ₁ Γ₂ A : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              (φ : sheaf_predicate (Γ₂ ×P A))
    : (∃h φ) [ s ]
      ⊢
      (∃h (φ [ BinProductOfArrows
                 _
                 (sheaf_binproducts C _ _)
                 (sheaf_binproducts C _ _)
                 s (identity _) ])).
  Proof.
    intros x₁ x₂ f xx.
    use contains_closure_sieve.
    intros y g.
    use factor_through_squash_hProp.
    intros [ aa p ].
    cbn in aa, p.
    use closure_sieve_contains.
    use hinhpr.
    cbn ; unfold prodtofuntoprod ; cbn.
    refine (aa ,, _).
    refine (from_sieve_eq_r
              (sieve_eq_from_closed
                 (psh_term_pt_eq
                    φ
                    (maponpaths
                       (λ z, z ,, aa)
                       (eqtohomot (nat_trans_ax (pr1 s) _ _ g) _))))
              _
              _).
    cbn.
    rewrite id_left.
    exact p.
  Qed.

  (** * 10. Equality *)
  Local Close Scope sh.

  Proposition is_closed_eq_sheaf_predicate_sieve
              {Γ : sheaf C}
              (φ : sheaf_predicate Γ)
              {x : C}
              (xx yy : (Γ x : hSet))
    : is_closed_sieve
        (eq_presheaf_predicate_sieve
           (sheaf_predicate_to_presheaf_predicate φ)
           xx
           yy).
  Proof.
    intros y g p ; cbn.
    split.
    - use closed_sieve_closed.
      use (site_trans_sieve p).
      cbn ; intros z h q.
      use sieve_contains_closed ; cbn.
      exact (pr1 q).
    - use (sheaf_amalgamation_unique _ p).
      + exact (is_sheaf_sheaf Γ).
      + use make_matching_family.
        * exact (λ z h _, #Γ (h · g) xx).
        * cbn ; intros z₁ z₂ h₁ h₂ h₃ q r₁ r₂.
          induction q.
          refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _).
          cbn.
          rewrite assoc.
          apply idpath.
      + cbn ; intros z h q.
        exact (eqtohomot (!(functor_comp Γ _ _)) _).
      + cbn ; intros z h q.
        refine (eqtohomot (!(functor_comp Γ _ _)) _ @ !_) ; cbn.
        exact (pr2 q).
  Qed.

  Definition eq_sheaf_predicate_sieve
             {Γ : sheaf C}
             (φ : sheaf_predicate Γ)
             {x : C}
             (xx yy : (Γ x : hSet))
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (eq_presheaf_predicate_sieve
               (sheaf_predicate_to_presheaf_predicate φ)
               xx yy).
    - exact (is_closed_eq_sheaf_predicate_sieve φ xx yy).
  Defined.

  Local Open Scope sh.

  Definition eq_sheaf_predicate_data
             {Γ : sheaf C}
             (φ : sheaf_predicate Γ)
    : psh_term_data (subobject_classifier_dep_sheaf (Γ ×P Γ))
    := λ x xx, eq_sheaf_predicate_sieve φ (pr1 xx) (pr2 xx).

  Arguments eq_sheaf_predicate_data /.

  Proposition eq_sheaf_predicate_law
              {Γ : sheaf C}
              (φ : sheaf_predicate Γ)
    : psh_term_law (eq_sheaf_predicate_data φ).
  Proof.
    intros x₁ x₂ f xx.
    use closed_sieve_eq.
    apply (eq_presheaf_predicate_law (sheaf_predicate_to_presheaf_predicate φ)).
  Qed.

  Definition eq_sheaf_predicate
             {Γ : sheaf C}
             (φ : sheaf_predicate Γ)
    : sheaf_predicate (Γ ×P Γ).
  Proof.
    use make_psh_term.
    - exact (eq_sheaf_predicate_data φ).
    - exact (eq_sheaf_predicate_law φ).
  Defined.

  Proposition eq_sheaf_intro
              {Γ : sheaf C}
              (φ : sheaf_predicate Γ)
    : φ ⊢ (eq_sheaf_predicate φ) [ ⟨ nat_trans_id _ , nat_trans_id _ ⟩ ].
  Proof.
    intros x y f xx p ; cbn.
    refine (p ,, _).
    apply idpath.
  Qed.

  Proposition eq_sheaf_elim
              {Γ : sheaf C}
              {φ : sheaf_predicate Γ}
              {ψ : sheaf_predicate (Γ ×P Γ)}
              (p : φ ⊢ ψ [ ⟨ nat_trans_id _ , nat_trans_id _ ⟩ ])
    : (eq_sheaf_predicate φ) ⊢ ψ.
  Proof.
    exact (eq_presheaf_elim
             (φ := sheaf_predicate_to_presheaf_predicate φ)
             (ψ := sheaf_predicate_to_presheaf_predicate ψ)
             p).
  Qed.

  Definition equality_sheaf_predicate
             {Γ A : sheaf C}
             (τ₁ τ₂ : Γ ⟹ A)
    : sheaf_predicate Γ
    := psh_term_subst
         (binproduct_nat_trans _ _ _ _ _ _ τ₁ τ₂)
         (eq_sheaf_predicate (truth_sheaf_predicate A)).

  Local Notation "τ₁ ≡ τ₂" := (equality_sheaf_predicate τ₁ τ₂) : sh.

  (** * 11. The forcing relation *)
  Definition sheaf_forces
             {Γ : sheaf C}
             (x : C)
             (xx : (Γ x : hSet))
             (φ : sheaf_predicate Γ)
    : hProp
    := (φ x xx : closed_sieve x) x (identity _).

  Notation "x ⊩_{ xx } φ" := (sheaf_forces x xx φ) (at level 100) : sh.

  (** * 12. Properties of the forcing relation *)
  Proposition sheaf_forces_monotone
              {Γ : sheaf C}
              {x y : C}
              (g : y --> x)
              {xx : (Γ x : hSet)}
              {φ : sheaf_predicate Γ}
              (p : x ⊩_{xx} φ)
    : y ⊩_{#Γ g xx} φ.
  Proof.
    unfold sheaf_forces in *.
    apply (from_sieve_eq_r
             (sieve_eq_from_closed (psh_term_naturality φ g xx))
             (identity y)).
    cbn.
    refine (#ω (φ x xx : closed_sieve _) g _ p).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition sheaf_forces_local
              {Γ : sheaf C}
              {x : C}
              (xx : (Γ x : hSet))
              (φ : sheaf_predicate Γ)
              (ω : sieve x)
              (p : C x ω)
              (H : ∏ (y : C) (f : y --> x), ω y f → y ⊩_{ #Γ f xx } φ)
    : x ⊩_{xx} φ.
  Proof.
    unfold sheaf_forces in *.
    use closed_sieve_closed.
    rewrite id_precomp_sieve.
    use (site_trans_sieve p).
    intros y f q.
    specialize (H y f q).
    use sieve_contains_closed.
    pose (from_sieve_eq_l
            (sieve_eq_from_closed (psh_term_naturality φ f xx))
            _
            H)
      as r.
    cbn in r.
    rewrite id_left in r.
    exact r.
  Qed.

  Proposition forces_truth_sheaves
              {Γ : sheaf C}
              (x : C)
              (xx : (Γ x : hSet))
    : x ⊩_{xx} ⊤.
  Proof.
    cbn.
    exact tt.
  Qed.

  Proposition forces_false_sheaves
              {Γ : sheaf C}
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} ⊥) ≃ C x (false_sieve x).
  Proof.
    cbn.
    rewrite id_precomp_sieve.
    exact (idweq _).
  Qed.

  Proposition forces_and_sheaves
              {Γ : sheaf C}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : sheaf_predicate Γ)
    : (x ⊩_{xx} φ ∧ ψ)%sh ≃ ((x ⊩_{xx} φ) × (x ⊩_{xx} ψ)).
  Proof.
    exact (idweq _).
  Qed.

  Proposition forces_or_sheaves
              {Γ : sheaf C}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : sheaf_predicate Γ)
    : (x ⊩_{xx} φ ∨ ψ)%sh
      ≃
      (∃ (ω : sieve x),
       (C x ω)
       ×
       (∏ (y : C) (g : y --> x), ω y g → (y ⊩_{ #Γ g xx } φ) ∨ (y ⊩_{ #Γ g xx } ψ))).
  Proof.
    use logeqweq.
    - intro p.
      use hinhpr.
      cbn in p.
      rewrite id_precomp_sieve in p.
      refine (disj_sieve (φ x xx : closed_sieve _) (ψ x xx : closed_sieve _) ,, _).
      refine (p ,, _).
      intros y g q.
      use (forces_or_presheaves
             y
             (#Γ g xx)
             (sheaf_predicate_to_presheaf_predicate φ)
             (sheaf_predicate_to_presheaf_predicate ψ)).
      revert q.
      use factor_through_squash_hProp.
      intros [ r | r ] ; cbn in r.
      + use hdisj_in1 ; cbn.
        pose (psh_term_naturality φ g xx) as r'.
        cbn in r'.
        rewrite r'.
        cbn.
        rewrite id_left.
        exact r.
      + use hdisj_in2 ; cbn.
        pose (psh_term_naturality ψ g xx) as r'.
        cbn in r'.
        rewrite r'.
        cbn.
        rewrite id_left.
        exact r.
    - use factor_through_squash_hProp.
      intros ( ω & p₁ & p₂ ).
      cbn.
      rewrite id_precomp_sieve.
      use (site_trans_sieve p₁).
      intros y h q.
      specialize (p₂ y h q).
      revert p₂.
      use factor_through_squash_hProp.
      intros [ r | r ].
      + use sieve_contains_closed.
        use hdisj_in1 ; cbn.
        unfold sheaf_forces in r.
        pose (from_sieve_eq_l
                (sieve_eq_from_closed (psh_term_naturality φ h xx))
                _
                r)
          as r'.
        cbn in r'.
        rewrite id_left in r'.
        exact r'.
      + use sieve_contains_closed.
        use hdisj_in2 ; cbn.
        unfold sheaf_forces in r.
        pose (from_sieve_eq_l
                (sieve_eq_from_closed (psh_term_naturality ψ h xx))
                _
                r)
          as r'.
        cbn in r'.
        rewrite id_left in r'.
        exact r'.
  Qed.

  Proposition forces_impl_sheaves
              {Γ : sheaf C}
              (x : C)
              (xx : (Γ x : hSet))
              (φ ψ : sheaf_predicate Γ)
    : (x ⊩_{xx} φ ⇒ ψ)
      ≃
      (∀ (y : C) (g : y --> x), (y ⊩_{#Γ g xx} φ) ⇒ (y ⊩_{#Γ g xx} ψ))%logic.
  Proof.
    exact (forces_impl_presheaves
             x xx
             (sheaf_predicate_to_presheaf_predicate φ)
             (sheaf_predicate_to_presheaf_predicate ψ)).
  Qed.

  Proposition forces_equality_sheaves
              {Γ A : sheaf C}
              (τ₁ τ₂ : Γ ⟹ A)
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} τ₁ ≡ τ₂)
      ≃
      (τ₁ x xx = τ₂ x xx)%logic.
  Proof.
    exact (forces_equality_presheaves τ₁ τ₂ x xx).
  Qed.

  Proposition forces_forall_sheaves
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} ∀h φ)
      ≃
      (∀ (y : C) (g : y --> x) (a : (A y : hSet)),
       y ⊩_{((#Γ g xx ,, a) : (Γ ×P A) y : hSet)} φ).
  Proof.
    exact (forces_forall_presheaves (sheaf_predicate_to_presheaf_predicate φ) x xx).
  Qed.

  Proposition forces_exists_sheaves
              {Γ A : sheaf C}
              (φ : sheaf_predicate (Γ ×P A))
              (x : C)
              (xx : (Γ x : hSet))
    : (x ⊩_{xx} exists_sheaf_predicate φ)
      ≃
      (∃ (ω : sieve x),
       (C x ω)
       ×
       (∏ (y : C) (g : y --> x),
        ω y g
        → ∃ (a : (A y : hSet)), y ⊩_{((#Γ g xx ,, a) : (Γ ×P A) y : hSet)} φ)).
  Proof.
    use logeqweq.
    - intro p.
      use hinhpr.
      cbn in p.
      rewrite id_precomp_sieve in p.
      refine (_ ,, p ,, _).
      clear p.
      intros y g p.
      exact p.
    - use factor_through_squash_hProp.
      intros ( ω & p & H ) ; cbn.
      rewrite id_precomp_sieve.
      use (site_trans_sieve p).
      intros y g q.
      specialize (H y g q).
      revert H.
      use factor_through_squash_hProp.
      intros ( a & r ).
      use (sieve_contains_closed (exists_presheaf_sieve _ _) g).
      use hinhpr ; cbn.
      exact (a ,, r).
  Qed.

  Proposition forces_entailment_sheaves
              {Γ : sheaf C}
              {φ : sheaf_predicate Γ}
    : (⊤ ⊢ φ)
      ≃
      ∀ (x : C) (xx : (Γ x : hSet)), x ⊩_{xx} φ.
  Proof.
    exact (forces_entailment_presheaves (sheaf_predicate_to_presheaf_predicate φ)).
  Qed.
End SheafLogic.

Notation "x ⊩_{ xx } φ" := (sheaf_forces x xx φ) (at level 100) : sh.
