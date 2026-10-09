(**

 Properties of hyperdoctrines

 In this file, we consider various properties that a first-order hyperdoctrine may satisfy.
 These are
 - Extensionality
 - Comprehension
 - Functional completeness
 We also consider extensionality for propositions and powersets in weak triposes.

 In an extensional hyperdoctrine, we can verify the equality of morphisms in the category of
 types and morphisms via the equality formula. This requirement is similar to functional
 extensionality. We can use it to check whether a morphism is a monomorphism using the
 internal language.

 Hyperdoctrines can also come with a comprehension operation. However, comprehension in
 hyperdoctrines comes with different ideas than comprehension in comprehension categories.
 The goal of a comprehension operation for hyperdoctrines is giving subtypes: if we have
 a type `A` together with a formula `φ` in context `A`, then comprehension gives us a subtype
 of `A`. We write `{ A | φ }` for the comprehension. Specifically, comprehension is given by
 a displayed functor from formulas to monomorphisms over the identity. In essence, the main
 requirement for this functor are that terms of type `{ A | φ }` are the same as terms of
 type `A` for which `φ` holds. This is not required for comprehension categories.

 Functional completeness allows one to make morphisms in the category of types and terms
 using functional relations. To define a morphism from `A` to `B`, it suffices to give a
 formula in context `A ×h B` that is a functional relation. The use case for functional
 completeness is that we can use the internal language to construct morphisms.

 Propositional extensionality is the same as univalence for the generic predicate, which
 functions as `hProp` in a tripos. We derive  propositional extensionality from a more
 general principle, namely an equality principle for the powerset.

 Contents
 1. Extensional hyperdoctrines
 2. Comprehension
 3. Functional completeness
 4. Extensionality for the power set

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Extensional hyperdoctrines *)
Definition extensional_first_order_hyperdoctrine
           (H : first_order_hyperdoctrine)
  : UU
  := ∏ (A B : ty H)
       (f g : A --> B),
     (⊤ ⊢ ∀h (f [ π₂ (tm_var (𝟙 ×h A)) ]tm ≡ g [ π₂ (tm_var _) ]tm))
     →
     f = g.

Definition isInjective_hyperdoctrine
           {H : first_order_hyperdoctrine}
           {A B : ty H}
           (f : A --> B)
  : form (𝟙 : ty H)
  := (∀h ∀h
      let a₁ := π₂ (π₁ (tm_var _)) in
      let a₂ := π₂ (tm_var _) in
      f [ a₁ ]tm ≡ f [ a₂ ]tm ⇒ a₁ ≡ a₂).

Proposition isInjective_hyperdoctrine_eq
            {H : first_order_hyperdoctrine}
            {A B : ty H}
            {f : A --> B}
            {Γ : ty H}
            {Δ : form Γ}
            (Hf : ⊤ ⊢ isInjective_hyperdoctrine f)
            (a₁ a₂ : tm Γ A)
            (p : Δ ⊢ f [ a₁ ]tm ≡ f [ a₂ ]tm)
  : Δ ⊢ a₁ ≡ a₂.
Proof.
  pose (hyperdoctrine_proof_subst (!! : Γ --> _) Hf) as q.
  unfold isInjective_hyperdoctrine in q.
  rewrite truth_subst, !forall_subst in q.
  pose (forall_elim q a₁) as q'.
  rewrite !forall_subst in q'.
  pose (forall_elim q' a₂) as r.
  refine (hyperdoctrine_cut p _).
  refine (weaken_cut _ _).
  {
    refine (hyperdoctrine_cut _ r).
    apply truth_intro.
  }
  simplify.
  refine (impl_elim _ _).
  - use weaken_left.
    apply hyperdoctrine_hyp.
  - use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition isMonic_extensional_first_order_hyperdoctrine
            {H : first_order_hyperdoctrine}
            (Hext : extensional_first_order_hyperdoctrine H)
            {A B : ty H}
            (f : A --> B)
            (Hf : ⊤ ⊢ isInjective_hyperdoctrine f)
  : isMonic f.
Proof.
  intros Γ x₁ x₂ p.
  use Hext.
  use forall_intro.
  simplify.
  use (isInjective_hyperdoctrine_eq Hf).
  use hyperdoctrine_refl_eq.
  unfold tm_subst, tm_var ; cbn.
  rewrite !assoc'.
  apply maponpaths.
  exact p.
Qed.

(** * 2. Comprehension *)
Definition first_order_hyperdoctrine_comprehension
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (χ : disp_functor
              (functor_identity _)
              (hyperdoctrine_formula_disp_cat H)
              (disp_mono_codomain _)),
     (∏ (A : ty H) (φ : form A),
      ⊤ ⊢ φ [ MonicArrow _ (mono_cod_mor (χ A φ)) ])
     ×
     (∏ (Γ A : ty H)
        (φ : form A)
        (t : tm Γ A)
        (p : ⊤ ⊢ φ [ t ]),
      ∃! (f : tm Γ (mono_cod_dom (χ A φ))),
      (MonicArrow _ (mono_cod_mor (χ A φ))) [ f ]tm = t).

Definition make_first_order_hyperdoctrine_comprehension
           {H : first_order_hyperdoctrine}
           (χ : disp_functor
                  (functor_identity _)
                  (hyperdoctrine_formula_disp_cat H)
                  (disp_mono_codomain _))
           (p : ∏ (A : ty H) (φ : form A),
                ⊤ ⊢ φ [ MonicArrow _ (mono_cod_mor (χ A φ)) ])
           (q : ∏ (Γ A : ty H)
                  (φ : form A)
                  (t : tm Γ A)
                  (p : ⊤ ⊢ φ [ t ]),
                ∃! (f : tm Γ (mono_cod_dom (χ A φ))),
                (MonicArrow _ (mono_cod_mor (χ A φ))) [ f ]tm = t)
  : first_order_hyperdoctrine_comprehension H
  := χ ,, p ,, q.

Section Comprehension.
  Context {H : first_order_hyperdoctrine}
          (χ : first_order_hyperdoctrine_comprehension H).

  Definition functor_of_comprehension
    : disp_functor
        (functor_identity _)
        (hyperdoctrine_formula_disp_cat H)
        (disp_mono_codomain _)
    := pr1 χ.

  Definition formula_comprehension
             {A : ty H}
             (φ : form A)
    : ty H
    := mono_cod_dom (functor_of_comprehension A φ).

  Definition formula_inclusion
             {A : ty H}
             (φ : form A)
    : formula_comprehension φ --> A
    := mono_cod_mor (functor_of_comprehension A φ).

  Definition formula_comprehension_sub
             {A : ty H}
             {φ ψ : form A}
             (p : φ ⊢ ψ)
    : formula_comprehension φ --> formula_comprehension ψ
    := mono_dom_mor (♯functor_of_comprehension p)%mor_disp.

  Proposition formula_comprehension_sub_eq
              {A : ty H}
              {φ ψ : form A}
              (p : φ ⊢ ψ)
    : formula_comprehension_sub p · formula_inclusion ψ = formula_inclusion φ.
  Proof.
    exact (mono_mor_eq (♯functor_of_comprehension p)%mor_disp).
  Defined.

  Proposition formula_comprehension_prf
              {A : ty H}
              (φ : form A)
    : ⊤ ⊢ φ [ formula_inclusion φ ].
  Proof.
    exact (pr12 χ A φ).
  Defined.

  Proposition formula_comprehension_prf_tm
              {A : ty H}
              {φ : form A}
              {Γ : ty H}
              (Δ : form Γ)
              (t : tm Γ (formula_comprehension φ))
    : Δ ⊢ φ [ (formula_inclusion φ) [ t ]tm ].
  Proof.
    pose (hyperdoctrine_proof_subst t (formula_comprehension_prf φ)) as q.
    rewrite truth_subst in q.
    rewrite hyperdoctrine_comp_subst in q.
    refine (hyperdoctrine_cut _ q).
    apply truth_intro.
  Qed.

  Definition make_comprehension_term
             {Γ A : ty H}
             (φ : form A)
             (t : tm Γ A)
             (p : ⊤ ⊢ φ [ t ])
    : tm Γ (formula_comprehension φ)
    := pr11 (pr22 χ Γ A φ t p).

  Proposition make_comprehension_term_eq
              {Γ A : ty H}
              (φ : form A)
              (t : tm Γ A)
              (p : ⊤ ⊢ φ [ t ])
    : (formula_inclusion φ) [ make_comprehension_term φ t p ]tm = t.
  Proof.
    exact (pr21 (pr22 χ Γ A φ t p)).
  Defined.

  Proposition eq_comprehension_term
              {Γ A : ty H}
              {φ : form A}
              {t₁ t₂ : tm Γ (formula_comprehension φ)}
              (p : (formula_inclusion φ) [ t₁ ]tm
                   =
                   (formula_inclusion φ) [ t₂ ]tm)
    : t₁ = t₂.
  Proof.
    refine (maponpaths
              pr1
              (proofirrelevance
                 _
                 (isapropifcontr (pr22 χ Γ A φ ((formula_inclusion φ) [ t₁ ]tm) _))
                 (_ ,, _)
                 (_ ,, _))).
    - apply formula_comprehension_prf_tm.
    - apply idpath.
    - exact (!p).
  Qed.
End Comprehension.

(** * 3. Functional completeness *)
Definition relation_with_images
           {H : first_order_hyperdoctrine}
           {A B : ty H}
           (φ : form (A ×h B))
  : form (𝟙 : ty H)
  := (∀h ∃h
      let a := π₂ (π₁ (tm_var _)) : tm _ A in
      let b := π₂ (tm_var _) : tm _ B in
      (φ [ ⟨ a , b ⟩ ])).

Definition relation_unique_images
           {H : first_order_hyperdoctrine}
           {A B : ty H}
           (φ : form (A ×h B))
  : form (𝟙 : ty H)
  := (∀h ∀h ∀h
      let a := π₂ (π₁ (π₁ (tm_var _))) in
      let b₁ := π₂ (π₁ (tm_var _)) in
      let b₂ := π₂ (tm_var _) in
      (φ [ ⟨ a , b₁ ⟩ ] ⇒ φ [ ⟨ a , b₂ ⟩ ] ⇒ b₁ ≡ b₂)).

Definition functional_relation
           {H : first_order_hyperdoctrine}
           {A B : ty H}
           (φ : form (A ×h B))
  : form (𝟙 : ty H)
  := relation_with_images φ ∧ relation_unique_images φ.

Proposition functional_relation_im
            {H : first_order_hyperdoctrine}
            {A B : ty H}
            (φ : form (A ×h B))
            (p : ⊤ ⊢ functional_relation φ)
            {Γ : ty H}
            (Δ : form Γ)
            (a : tm Γ A)
  : (Δ ⊢ ∃h (φ [ ⟨ a [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ])).
Proof.
  pose (hyperdoctrine_proof_subst (!! : Γ --> _) p) as q.
  rewrite truth_subst in q.
  refine (hyperdoctrine_cut (hyperdoctrine_cut (truth_intro _) q) _).
  unfold functional_relation, relation_with_images.
  simplify.
  use weaken_left.
  refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) a) _).
  simplify.
  apply hyperdoctrine_hyp.
Qed.

Proposition functional_relation_unique_im
            {H : first_order_hyperdoctrine}
            {A B : ty H}
            (φ : form (A ×h B))
            (p : ⊤ ⊢ functional_relation φ)
            {Γ : ty H}
            (Δ : form Γ)
            (a : tm Γ A)
            (b₁ b₂ : tm Γ B)
            (q₁ : Δ ⊢ φ [ ⟨ a , b₁ ⟩ ])
            (q₂ : Δ ⊢ φ [ ⟨ a , b₂ ⟩ ])
  : Δ ⊢ b₁ ≡ b₂.
Proof.
  pose (hyperdoctrine_proof_subst (!! : Γ --> _) p) as q.
  rewrite truth_subst in q.
  use (impl_elim q₂).
  use (impl_elim q₁).
  refine (hyperdoctrine_cut (hyperdoctrine_cut (truth_intro _) q) _).
  unfold functional_relation, relation_unique_images.
  simplify.
  use weaken_right.
  refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) a) _).
  simplify.
  refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) b₁) _).
  simplify.
  refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) b₂) _).
  simplify.
  apply hyperdoctrine_hyp.
Qed.

Definition agrees_with_relation
           {H : first_order_hyperdoctrine}
           {A B : ty H}
           (φ : form (A ×h B))
           (f : A --> B)
  : form (𝟙 : ty H)
  := (∀h
      let a := π₂ (tm_var _) in
      φ [ ⟨ a , f [ a ]tm ⟩ ]).

Definition first_order_hyperdoctrine_functional_completeness
           (H : first_order_hyperdoctrine)
  : UU
  := ∏ (A B : ty H)
       (φ : form (A ×h B))
       (p : ⊤ ⊢ functional_relation φ),
     ∑ (f : A --> B),
     (⊤ ⊢ agrees_with_relation φ f).

Definition functional_relation_to_mor
           {H : first_order_hyperdoctrine}
           (HH : first_order_hyperdoctrine_functional_completeness H)
           {A B : ty H}
           (φ : form (A ×h B))
           (p : ⊤ ⊢ functional_relation φ)
  : A --> B
  := pr1 (HH A B φ p).

Proposition functional_relation_to_mor_agrees
            {H : first_order_hyperdoctrine}
            (HH : first_order_hyperdoctrine_functional_completeness H)
            {A B : ty H}
            (φ : form (A ×h B))
            (p : ⊤ ⊢ functional_relation φ)
            {Γ : ty H}
            (Δ : form Γ)
            (a : tm Γ A)
  : Δ ⊢ φ [ ⟨ a , (functional_relation_to_mor HH φ p) [ a ]tm ⟩ ].
Proof.
  pose (hyperdoctrine_proof_subst (!! : Γ --> _) (pr2 (HH A B φ p))) as q.
  rewrite truth_subst in q.
  refine (hyperdoctrine_cut (hyperdoctrine_cut (truth_intro _) q) _).
  unfold agrees_with_relation.
  rewrite forall_subst.
  refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) a) _).
  simplify.
  apply hyperdoctrine_hyp.
Qed.

(** * 4. Extensionality for the powerset *)
Local Open Scope weak_tripos.

Definition power_ext_weak_tripos
           (H : weak_tripos)
  : UU
  := ∏ (A : ty H),
     let a := π₂ (tm_var (((𝟙 ×h ℙ A) ×h ℙ A) ×h A)) in
     let φ := π₂ (π₁ (tm_var _)) in
     let ψ := π₂ (π₁ (π₁ (tm_var _))) in
     ⊤ ⊢ (∀h ∀h ((∀h (a ∈ φ ⇔ a ∈ ψ))
                 ⇒
                 π₂ (π₁ (tm_var _)) ≡ π₂ (tm_var _))).

Proposition power_ext_weak_tripos_set_eq
            {H : weak_tripos}
            (HPE : power_ext_weak_tripos H)
            {Γ A : ty H}
            {Δ : form Γ}
            {φ ψ : tm Γ (ℙ A)}
            (p : Δ ⊢ ∀h (π₂ (tm_var _) ∈ φ [ π₁ (tm_var _) ]tm
                         ⇒
                         π₂ (tm_var _) ∈ ψ [ π₁ (tm_var _) ]tm))
            (q : Δ ⊢ ∀h (π₂ (tm_var _) ∈ ψ [ π₁ (tm_var _) ]tm
                         ⇒
                         π₂ (tm_var _) ∈ φ [ π₁ (tm_var _) ]tm))
  : Δ ⊢ φ ≡ ψ.
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    refine (conj_intro p _).
    refine (conj_intro q _).
    refine (hyperdoctrine_cut _ (hyperdoctrine_proof_subst !! (HPE A))).
    hypersimplify.
    apply truth_intro.
  }
  use hyp_rtrans.
  use hyp_sym.
  hypersimplify.
  refine (weaken_cut _ _).
  {
    use weaken_left.
    refine (forall_elim (hyperdoctrine_hyp _) _).
    exact φ.
  }
  use hyp_ltrans.
  use weaken_right.
  use hyp_sym.
  hypersimplify.
  refine (weaken_cut _ _).
  {
    use weaken_left.
    refine (forall_elim (hyperdoctrine_hyp _) _).
    exact ψ.
  }
  use hyp_ltrans.
  use weaken_right.
  hypersimplify.
  refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
  use weaken_left.
  use forall_intro.
  pose (a := π₂ (tm_var (Γ ×h A))).
  hypersimplify.
  refine (weaken_cut _ _).
  {
    use weaken_left.
    refine (forall_elim (hyperdoctrine_hyp _) _).
    exact (π₂ (tm_var _)).
  }
  use hyp_ltrans.
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
  fold a.
  use iff_intro.
  - use hyp_ltrans.
    use weaken_right.
    refine (impl_elim _ _).
    + use weaken_right.
      apply hyperdoctrine_hyp.
    + use weaken_left.
      apply hyperdoctrine_hyp.
  - refine (impl_elim _ _).
    + use weaken_right.
      apply hyperdoctrine_hyp.
    + do 2 use weaken_left.
      apply hyperdoctrine_hyp.
Qed.

#[local] Transparent prf_of_weak_generic_predicate.

Proposition prop_ext_weak_tripos
            {H : weak_tripos}
            (HPE : power_ext_weak_tripos H)
            {Γ : ty H}
            {Δ : form Γ}
            {ω₁ ω₂ : tm Γ Ω}
            (p : Δ ⊢ Prf [ ω₁ ] ⇒ Prf [ ω₂ ])
            (q : Δ ⊢ Prf [ ω₂ ] ⇒ Prf [ ω₁ ])
  : Δ ⊢ ω₁ ≡ ω₂.
Proof.
  use (power_ext_weak_tripos_set_eq HPE).
  - use forall_intro.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_proof_subst _ p).
    }
    cbn.
    hypersimplify.
    rewrite !(hyperdoctrine_unit_eta (π₂ (tm_var (Γ ×h 𝟙)))).
    apply hyperdoctrine_hyp.
  - use forall_intro.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_proof_subst _ q).
    }
    cbn.
    hypersimplify.
    rewrite !(hyperdoctrine_unit_eta (π₂ (tm_var (Γ ×h 𝟙)))).
    apply hyperdoctrine_hyp.
Qed.

Local Close Scope weak_tripos.
Local Open Scope tripos.

Definition power_ext_tripos
           (H : tripos)
  : UU
  := power_ext_weak_tripos (tripos_to_weak_tripos H).

Proposition power_ext_tripos_set_eq
            {H : tripos}
            (HPE : power_ext_tripos H)
            {Γ A : ty H}
            {Δ : form Γ}
            {φ ψ : tm Γ (ℙ A)}
            (p : Δ ⊢ ∀h (π₂ (tm_var _) ∈ φ [ π₁ (tm_var _) ]tm
                         ⇒
                         π₂ (tm_var _) ∈ ψ [ π₁ (tm_var _) ]tm))
            (q : Δ ⊢ ∀h (π₂ (tm_var _) ∈ ψ [ π₁ (tm_var _) ]tm
                         ⇒
                         π₂ (tm_var _) ∈ φ [ π₁ (tm_var _) ]tm))
  : Δ ⊢ φ ≡ ψ.
Proof.
  use (power_ext_weak_tripos_set_eq HPE).
  - exact p.
  - exact q.
Qed.

Proposition prop_ext_tripos
            {H : tripos}
            (HPE : power_ext_tripos H)
            {Γ : ty H}
            {Δ : form Γ}
            {ω₁ ω₂ : tm Γ Ω}
            (p : Δ ⊢ Prf [ ω₁ ] ⇒ Prf [ ω₂ ])
            (q : Δ ⊢ Prf [ ω₂ ] ⇒ Prf [ ω₁ ])
  : Δ ⊢ ω₁ ≡ ω₂.
Proof.
  use (prop_ext_weak_tripos HPE).
  - exact p.
  - exact q.
Qed.
