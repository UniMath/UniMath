(**********************************************************************************************

 Triposes

 In the literature, various examples of toposes have been established. Among those, are
 1. Realizability toposes, which arise from partial combinatory algebras.
 2. Sets valued in a complete Heyting algebra.
 These examples can be captured in various general frameworks, and one of them is given by
 triposes. In essence, a tripos is a place where one can interpret first-order predicate logic
 and where one has power sets. Concretely, this means that a tripos is given by a first-order
 hyperdoctrine such that for every object `X` there is a powerset object `PX` and a membership
 predicate on `X ×h PX`. There also is some kind of universal property that relates predicates
 on `X` in context `Γ` and terms of type `PX`. This is expressed by the axiom (CA) in the
 paper "Tripos Theory in Retrospect" by Andrew Pitts. This file gives the definition of
 triposes.

 The universal property of power sets can be expressed in two ways, and this gives rise to the
 notion of tripos and that of weak tripos. In "Tripos Theory in Retrospect" by Andrew Pitts,
 it is shown that any first-order hyperdoctrine that satisfies the axiom CA (Axiom 4.1) gives
 rise to a topos. This axiom is fully expressed in the logic of the first-order hyperdoctrine,
 and we say that a weak tripos is a first-order hyperdoctrine satisfying axiom CA. Note that
 this axiom is both necessary and sufficient (Theorem 4.2). However, in practice, examples
 satisfy a stronger condition, which is given in Definition 4.3. Definition 4.3 is not
 expressed in the internal language of the hyperdoctrine, but instead witnesses are given.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Triposes
 2. Some substitutions necessary to define weak triposes
 3. The definition of weak triposes
 4. Every tripos is a weak tripos

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.

Local Open Scope cat.
Local Open Scope hd.

Declare Scope tripos.
Delimit Scope tripos with tripos.

Declare Scope weak_tripos.
Delimit Scope weak_tripos with weak_tripos.

(** * 1. Tripos *)
Definition is_power_object_tripos
           {H : preorder_hyperdoctrine}
           (X : ty H)
           (PX : ty H)
           (inX : form (X ×h PX))
  : UU
  := ∏ (Γ : ty H)
       (R : form (X ×h Γ)),
     ∑ (f : tm Γ PX),
     R
     =
     inX [ ⟨ π₁ (tm_var _) , f [ π₂ (tm_var _) ]tm ⟩ ].

Definition is_preorder_tripos
           (H : preorder_hyperdoctrine)
  : UU
  := ∏ (X : ty H),
     ∑ (PX : ty H)
       (inX : form (X ×h PX)),
     is_power_object_tripos X PX inX.

Definition preorder_tripos
  : UU
  := ∑ (H : first_order_preorder_hyperdoctrine), is_preorder_tripos H.

Coercion preorder_tripos_to_first_order_hyperdoctrine
         (H : preorder_tripos)
  : first_order_preorder_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Definition is_tripos
           (H : hyperdoctrine)
           (H' := hyperdoctrine_to_preorder_hyperdoctrine H)
  : UU
  := ∏ (X : ty H'),
     ∑ (PX : ty H')
       (inX : form (X ×h PX)),
     is_power_object_tripos X PX inX.

Definition tripos
  : UU
  := ∑ (H : first_order_hyperdoctrine), is_tripos H.

Coercion tripos_to_first_order_hyperdoctrine
         (H : tripos)
  : first_order_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Local Open Scope tripos.

Definition tripos_power
           {H : tripos}
           (X : ty H)
  : ty H
  := pr1 (pr2 H X).

Notation "'ℙ'" := tripos_power : tripos. (* \bP *)

Definition tripos_in
           {H : tripos}
           (X : ty H)
  : form (X ×h ℙ X)
  := pr12 (pr2 H X).

Notation "x ∈ P" := ((tripos_in _) [ ⟨ x , P ⟩ ]) : tripos.

Proposition tripos_in_subst
            {H : tripos}
            {Γ₁ Γ₂ X : ty H}
            (x : tm Γ₂ X)
            (P : tm Γ₂ (ℙ X))
            (s : tm Γ₁ Γ₂)
  : (x ∈ P) [ s ]
    =
    ((x [ s ]tm) ∈ (P [ s ]tm)).
Proof.
  unfold tripos_in.
  hypersimplify.
  apply idpath.
Qed.

Definition tripos_compr
           {H : tripos}
           {X : ty H}
           {Γ : ty H}
           (R : form (X ×h Γ))
  : tm Γ (ℙ X)
  := pr1 (pr22 (pr2 H X) Γ R).

Notation "{{ R }}" := (tripos_compr R) : tripos.

Proposition mor_to_tripos_power_eq
            {H : tripos}
            (X : ty H)
            (Γ : ty H)
            (R : form (X ×h Γ))
            (x := π₁ (tm_var (X ×h Γ)))
            (γ := π₂ (tm_var (X ×h Γ)))
  : R = (x ∈ ({{ R }} [ γ ]tm)).
Proof.
  exact (pr2 (pr22 (pr2 H X) Γ R)).
Qed.

Proposition mor_to_tripos_power_f
            {H : tripos}
            (X : ty H)
            (Γ : ty H)
            (R : form (X ×h Γ))
            (Δ : form (X ×h Γ))
            (x := π₁ (tm_var (X ×h Γ)))
            (γ := π₂ (tm_var (X ×h Γ)))
            (p : Δ ⊢ R)
  : Δ ⊢ x ∈ ({{ R }} [ γ ]tm).
Proof.
  refine (hyperdoctrine_cut p _).
  exact (hyperdoctrine_formula_eq_f (mor_to_tripos_power_eq  X Γ R)).
Qed.

Proposition mor_to_tripos_power_b
            {H : tripos}
            (X : ty H)
            (Γ : ty H)
            (R : form (X ×h Γ))
            (Δ : form (X ×h Γ))
            (x := π₁ (tm_var (X ×h Γ)))
            (γ := π₂ (tm_var (X ×h Γ)))
            (p : Δ ⊢ x ∈ {{ R }} [ γ ]tm)
  : Δ ⊢ R.
Proof.
  refine (hyperdoctrine_cut p _).
  exact (hyperdoctrine_formula_eq_b (mor_to_tripos_power_eq  X Γ R)).
Qed.

Definition make_tripos
           (H : first_order_hyperdoctrine)
           (HH : is_tripos H)
  : tripos
  := H ,, HH.

(** * 2. Some substitutions necessary to define weak triposes *)
Definition hyperdoctrine_sub_pr_1_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) A
  := π₁ (π₁ (π₁ (tm_var _))).

Definition hyperdoctrine_sub_pr_2_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) B
  := π₂ (π₁ (π₁ (tm_var _))).

Definition hyperdoctrine_sub_pr_3_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) C
  := π₂ (π₁ (tm_var _)).

Definition hyperdoctrine_sub_pr_4_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) D
  := π₂ (tm_var _).

Definition hyperdoctrine_sub_pr_4_3
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) (D ×h C)
  := ⟨ hyperdoctrine_sub_pr_4_of_4 , hyperdoctrine_sub_pr_3_of_4 ⟩.

Definition hyperdoctrine_sub_pr_4_2
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) (D ×h B)
  := ⟨ hyperdoctrine_sub_pr_4_of_4 , hyperdoctrine_sub_pr_2_of_4 ⟩.

Arguments hyperdoctrine_sub_pr_1_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_2_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_3_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_3 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_2 {_ _ _ _ _} /.

Close Scope tripos.

(** * 3. The definition of weak triposes *)
Local Open Scope weak_tripos.

Definition is_weak_tripos_law
           {H : first_order_hyperdoctrine}
           {X : ty H}
           {PX : ty H}
           (inX : form (X ×h PX))
  : UU
  := ∏ (Γ : ty H)
       (R : form (X ×h Γ)),
     let s₁ := (hyperdoctrine_sub_pr_4_3 : tm (((𝟙 ×h Γ) ×h PX) ×h X) _) in
     let s₂ := (hyperdoctrine_sub_pr_4_2 : tm (((𝟙 ×h Γ) ×h PX) ×h X) _) in
     ⊤ ⊢ (∀h ∃h ∀h (inX [ s₁ ] ⇔ R [ s₂ ])).

Definition is_weak_tripos
           (H : first_order_hyperdoctrine)
  : UU
  := ∏ (X : ty H),
     ∑ (PX : ty H)
       (inX : form (X ×h PX)),
     is_weak_tripos_law inX.

Definition weak_tripos
  : UU
  := ∑ (H : first_order_hyperdoctrine), is_weak_tripos H.

Coercion weak_tripos_to_first_order_hyperdoctrine
         (H : weak_tripos)
  : first_order_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Definition make_weak_tripos
           (H : first_order_hyperdoctrine)
           (HH : is_weak_tripos H)
  : weak_tripos
  := H ,, HH.

Definition weak_tripos_power
           {H : weak_tripos}
           (X : ty H)
  : ty H
  := pr1 (pr2 H X).

Notation "'ℙ'" := weak_tripos_power : weak_tripos. (* \bP *)

Definition weak_tripos_in
           {H : weak_tripos}
           (X : ty H)
  : form (X ×h ℙ X)
  := pr12 (pr2 H X).

Notation "x ∈ P" := ((weak_tripos_in _) [ ⟨ x , P ⟩ ]) (at level 70) : weak_tripos.

Proposition weak_tripos_in_subst
            {H : weak_tripos}
            {Γ₁ Γ₂ X : ty H}
            (x : tm Γ₂ X)
            (P : tm Γ₂ (ℙ X))
            (s : tm Γ₁ Γ₂)
  : (x ∈ P) [ s ]
    =
    ((x [ s ]tm) ∈ (P [ s ]tm)).
Proof.
  unfold weak_tripos_in.
  hypersimplify.
  apply idpath.
Qed.

Definition weak_tripos_rel_equiv
           {H : weak_tripos}
           {X : ty H}
           {Γ₁ Γ₂ : ty H}
           (R : form (X ×h Γ₂))
           (γ : tm Γ₁ Γ₂)
           (t : tm Γ₁ (ℙ X))
  : form Γ₁
  := (∀h (π₂ (tm_var _) ∈ t [ π₁ (tm_var _) ]tm
          ⇔
          R [ ⟨ π₂ (tm_var _) , γ [ π₁ (tm_var _) ]tm ⟩ ])).

Proposition weak_tripos_rel_equiv_left
            {H : weak_tripos}
            {X : ty H}
            {Γ₁ Γ₂ : ty H}
            (R : form (X ×h Γ₂))
            (γ : tm Γ₁ Γ₂)
            (t : tm Γ₁ (ℙ X))
            (Δ : form Γ₁)
            (p : Δ ⊢ weak_tripos_rel_equiv R γ t)
            (x : tm Γ₁ X)
            (q : Δ ⊢ x ∈ t)
  : Δ ⊢ R [ ⟨ x , γ ⟩ ].
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    exact (conj_intro p q).
  }
  refine (hyperdoctrine_cut _ _).
  {
    refine (conj_intro _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact (forall_elim (hyperdoctrine_hyp _) x).
  }
  hypersimplify.
  refine (iff_elim_left _ _).
  - use weaken_left.
    apply hyperdoctrine_hyp.
  - use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition weak_tripos_rel_equiv_right
            {H : weak_tripos}
            {X : ty H}
            {Γ₁ Γ₂ : ty H}
            (R : form (X ×h Γ₂))
            (γ : tm Γ₁ Γ₂)
            (t : tm Γ₁ (ℙ X))
            (Δ : form Γ₁)
            (p : Δ ⊢ weak_tripos_rel_equiv R γ t)
            (x : tm Γ₁ X)
            (q : Δ ⊢ R [ ⟨ x , γ ⟩ ])
  : Δ ⊢ x ∈ t.
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    exact (conj_intro p q).
  }
  refine (hyperdoctrine_cut _ _).
  {
    refine (conj_intro _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact (forall_elim (hyperdoctrine_hyp _) x).
  }
  hypersimplify.
  refine (iff_elim_right _ _).
  - use weaken_left.
    apply hyperdoctrine_hyp.
  - use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Definition weak_tripos_compr
           {H : weak_tripos}
           {X : ty H}
           {Γ₁ Γ₂ : ty H}
           (R : form (X ×h Γ₂))
           (Δ : form Γ₁)
           (t : tm Γ₁ Γ₂)
  : Δ ⊢ (∃h (weak_tripos_rel_equiv R (t [ π₁ (tm_var _) ]tm) (π₂ (tm_var _)))).
Proof.
  unfold weak_tripos_rel_equiv.
  refine (hyperdoctrine_cut _ _).
  {
    refine (forall_elim _ t).
    refine (hyperdoctrine_cut (truth_intro _) _).
    refine (hyperdoctrine_cut
              (hyperdoctrine_cut
                 _
                 (hyperdoctrine_proof_subst _ (pr22 (pr2 H X) Γ₂ R)))
              _).
    {
      hypersimplify.
      use truth_intro.
    }
    simplify.
    apply hyperdoctrine_hyp.
  }
  hypersimplify_form.
  unfold hyperdoctrine_sub_pr_4_2, hyperdoctrine_sub_pr_4_3.
  unfold hyperdoctrine_sub_pr_4_of_4, hyperdoctrine_sub_pr_3_of_4.
  unfold hyperdoctrine_sub_pr_2_of_4.
  hypersimplify.
  apply hyperdoctrine_hyp.
Qed.

(** * 4. Every tripos is a weak tripos *)
Close Scope weak_tripos.
Local Open Scope tripos.

Proposition tripos_to_weak_tripos_law
            {H : tripos}
            (X : ty H)
  : is_weak_tripos_law (tripos_in X).
Proof.
  intros Γ R.
  use forall_intro.
  use exists_intro.
  - exact ({{ R }} [ π₂ (tm_var _) ]tm).
  - cbn ; hypersimplify.
    use forall_intro.
    pose (x := π₂ (tm_var ((𝟙 ×h Γ) ×h X))).
    pose (γ := π₂ (π₁ (tm_var ((𝟙 ×h Γ) ×h X)))).
    fold x γ.
    use iff_intro.
    + use weaken_right.
      refine (hyperdoctrine_cut
                _
                (hyperdoctrine_proof_subst
                   ⟨ x , γ ⟩
                   (mor_to_tripos_power_b X Γ R _ (hyperdoctrine_hyp _)))).
      rewrite tripos_in_subst.
      hypersimplify.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      refine (hyperdoctrine_cut
                (hyperdoctrine_proof_subst
                   ⟨ x , γ ⟩
                   (mor_to_tripos_power_f X Γ R _ (hyperdoctrine_hyp _)))
                _).
      rewrite tripos_in_subst.
      hypersimplify.
      apply hyperdoctrine_hyp.
Qed.

Definition tripos_to_is_weak_tripos
           (H : tripos)
  : is_weak_tripos H.
Proof.
  intros X.
  simple refine (_ ,, _ ,, _).
  - exact (ℙ X).
  - exact (tripos_in X).
  - exact (tripos_to_weak_tripos_law X).
Defined.

Definition tripos_to_weak_tripos
           (H : tripos)
  : weak_tripos
  := _ ,, tripos_to_is_weak_tripos H.
