(**

 Natural numbers in a first-order hyperdoctrine

 Our goal is to show that the topos arising from a tripos has a natural numbers
 object. To do so, we need to assume some additional properties of the tripos.
 Specifically, we need to assume the following:
 - we have a type `N`
 - we have terms `z : N` and `s : N -> N`
 - in the internal language, we can prove `s n ≠ z` and that we have `n = m`
   whenever we have `s n = s m`
 Under these assumptions, we can show that the tripos to topos construction
 comes with a natural numbers object.

 In this file, we establish the basic notions regarding natural numbers in a
 first-order hyperdoctrine.

 Content
 1. Natural numbers in a first-order hyperdoctrine
 2. Properties of natural numbers
 3. Natural numbers of the weak tripos associated to a tripos
 4. Natural numbers in a first-order preorder hyperdoctrine

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Natural numbers in a first-order hyperdoctrine *)
Definition first_order_hyperdoctrine_nats_data
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (N : ty H), tm 𝟙 N × tm N N.

Definition make_first_order_hyperdoctrine_nats_data
           {H : first_order_hyperdoctrine}
           (N : ty H)
           (z : tm 𝟙 N)
           (s : tm N N)
  : first_order_hyperdoctrine_nats_data H
  := N ,, z ,, s.

Coercion first_order_hyperdoctrine_nats_ty
         {H : first_order_hyperdoctrine}
         (N : first_order_hyperdoctrine_nats_data H)
  : ty H
  := pr1 N.

Definition hd_nats_z
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
           (Γ : ty H)
  : tm Γ N
  := pr12 N [ !! ]tm.

Proposition subst_hd_nats_z
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats_data H)
            {Γ₁ Γ₂ : ty H}
            (s : tm Γ₁ Γ₂)
  : (hd_nats_z N _) [ s ]tm = hd_nats_z N _.
Proof.
  unfold hd_nats_z.
  hypersimplify.
  apply idpath.
Qed.

Definition hd_nats_s
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
           {Γ : ty H}
           (n : tm Γ N)
  : tm Γ N
  := pr22 N [ n ]tm.

Proposition subst_hd_nats_s
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats_data H)
            {Γ₁ Γ₂ : ty H}
            (s : tm Γ₁ Γ₂)
            (n : tm Γ₂ N)
  : (hd_nats_s N n) [ s ]tm = hd_nats_s N (n [ s ]tm).
Proof.
  unfold hd_nats_s.
  hypersimplify.
  apply idpath.
Qed.

Proposition app_hd_nat_s
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats_data H)
            {Γ : ty H}
            {n m : tm Γ N}
            {Δ : form Γ}
            (p : Δ ⊢ n ≡ m)
  : Δ ⊢ hd_nats_s N n ≡ hd_nats_s N m.
Proof.
  unfold hd_nats_s.
  use hyperdoctrine_subst_eq.
  exact p.
Qed.

Definition first_order_hyperdoctrine_nats_zs_axiom
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
  : UU
  := let n := π₂ (tm_var (𝟙 ×h N)) in
     (⊤ ⊢ ∀h (¬(hd_nats_s N n ≡ hd_nats_z N _))).

Definition first_order_hyperdoctrine_nats_mono_axiom
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
  : UU
  := let n := π₂ (tm_var ((𝟙 ×h N) ×h N)) in
     let m := π₂ (π₁ (tm_var ((𝟙 ×h N) ×h N))) in
     (⊤ ⊢ ∀h ∀h (hd_nats_s N n ≡ hd_nats_s N m ⇒ n ≡ m)).

Definition first_order_hyperdoctrine_nats_axioms
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
  : UU
  := first_order_hyperdoctrine_nats_zs_axiom N
     ×
     first_order_hyperdoctrine_nats_mono_axiom N.

Definition first_order_hyperdoctrine_nats
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (N : first_order_hyperdoctrine_nats_data H),
     first_order_hyperdoctrine_nats_axioms N.

Definition make_first_order_hyperdoctrine_nats
           {H : first_order_hyperdoctrine}
           (N : first_order_hyperdoctrine_nats_data H)
           (P : first_order_hyperdoctrine_nats_axioms N)
  : first_order_hyperdoctrine_nats H
  := N ,, P.

Coercion first_order_hyperdoctrine_nats_to_data
         {H : first_order_hyperdoctrine}
         (N : first_order_hyperdoctrine_nats H)
  : first_order_hyperdoctrine_nats_data H
  := pr1 N.

(** * 2. Properties of natural numbers *)
Proposition first_order_hyperdoctrine_nats_z_neq_s
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats H)
            {Γ : ty H}
            {Δ : form Γ}
            (n : tm Γ N)
  : Δ ⊢ ¬ (hd_nats_s N n ≡ hd_nats_z N _).
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_proof_subst !! (pr12 N))).
    hypersimplify.
    apply truth_intro.
  }
  hypersimplify.
  refine (hyperdoctrine_cut _ _).
  {
    exact (forall_elim (hyperdoctrine_hyp _) n).
  }
  hypersimplify.
  rewrite !subst_hd_nats_z.
  rewrite !subst_hd_nats_s.
  rewrite hyperdoctrine_pr2_subst.
  rewrite var_tm_subst.
  rewrite hyperdoctrine_pair_pr2.
  apply hyperdoctrine_hyp.
Qed.

Proposition first_order_hyperdoctrine_nats_z_neq_s_all
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats H)
            {Γ : ty H}
            {Δ φ : form Γ}
            (n : tm Γ N)
            (p : Δ ⊢ hd_nats_s N n ≡ hd_nats_z N _)
  : Δ ⊢ φ.
Proof.
  refine (neg_elim p _).
  apply first_order_hyperdoctrine_nats_z_neq_s.
Qed.

Proposition first_order_hyperdoctrine_nats_s_mono
            {H : first_order_hyperdoctrine}
            (N : first_order_hyperdoctrine_nats H)
            {Γ : ty H}
            {Δ : form Γ}
            {n m : tm Γ N}
            (p : Δ ⊢ hd_nats_s N n ≡ hd_nats_s N m)
  : Δ ⊢ n ≡ m.
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    exact p.
  }
  refine (weaken_cut _ _).
  {
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_proof_subst !! (pr22 N))).
    hypersimplify.
    apply truth_intro.
  }
  hypersimplify.
  use hyp_sym.
  refine (weaken_cut _ _).
  {
    refine (forall_elim _ m).
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  use hyp_ltrans.
  use weaken_right.
  hypersimplify.
  use hyp_sym.
  refine (weaken_cut _ _).
  {
    refine (forall_elim _ n).
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  use hyp_ltrans.
  use weaken_right.
  hypersimplify.
  refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
  use weaken_left.
  rewrite !subst_hd_nats_s.
  rewrite !hyperdoctrine_pr2_subst.
  rewrite !hyperdoctrine_pr1_subst.
  rewrite !var_tm_subst.
  rewrite !hyperdoctrine_pair_pr2.
  rewrite !hyperdoctrine_pair_pr1.
  rewrite !hyperdoctrine_pair_pr2.
  apply hyperdoctrine_hyp.
Qed.

(** * 3. Natural numbers of the weak tripos associated to a tripos *)
Definition tripos_to_weak_tripos_nats
           (H : tripos)
           (N : first_order_hyperdoctrine_nats H)
  : first_order_hyperdoctrine_nats (tripos_to_weak_tripos H).
Proof.
  use make_first_order_hyperdoctrine_nats.
  - use make_first_order_hyperdoctrine_nats_data.
    + exact N.
    + exact (pr121 N).
    + exact (pr221 N).
  - split.
    + exact (pr12 N).
    + exact (pr22 N).
Defined.

(** * 4. Natural numbers in a first-order preorder hyperdoctrine *)
Definition first_order_preorder_hyperdoctrine_nats_data
           (H : first_order_preorder_hyperdoctrine)
  : UU
  := ∑ (N : ty H), tm 𝟙 N × tm N N.

Definition make_first_order_preorder_hyperdoctrine_nats_data
           {H : first_order_preorder_hyperdoctrine}
           (N : ty H)
           (z : tm 𝟙 N)
           (s : tm N N)
  : first_order_preorder_hyperdoctrine_nats_data H
  := N ,, z ,, s.

Coercion first_order_preorder_hyperdoctrine_nats_ty
         {H : first_order_preorder_hyperdoctrine}
         (N : first_order_preorder_hyperdoctrine_nats_data H)
  : ty H
  := pr1 N.

Definition hd_nats_z_pre
           {H : first_order_preorder_hyperdoctrine}
           (N : first_order_preorder_hyperdoctrine_nats_data H)
           (Γ : ty H)
  : tm Γ N
  := pr12 N [ !! ]tm.

Definition hd_nats_s_pre
           {H : first_order_preorder_hyperdoctrine}
           (N : first_order_preorder_hyperdoctrine_nats_data H)
           {Γ : ty H}
           (n : tm Γ N)
  : tm Γ N
  := pr22 N [ n ]tm.

Section PreorderHyperdoctrineAxioms.
  Context {H : first_order_preorder_hyperdoctrine}
          (N : first_order_preorder_hyperdoctrine_nats_data H).

  Local Notation "'⊤'" := first_order_preorder_hyperdoctrine_truth.
  Local Notation "'⊥'" := first_order_preorder_hyperdoctrine_false.
  Local Notation "φ ⇒ ψ" := (first_order_preorder_hyperdoctrine_impl φ ψ).
  Local Notation "'∀h' φ" := (first_order_preorder_hyperdoctrine_forall φ).
  Local Notation "t₁ ≡ t₂" := (first_order_preorder_hyperdoctrine_equal t₁ t₂).

  Definition first_order_preorder_hyperdoctrine_nats_zs_axiom
    : UU
    := let n := π₂ (tm_var (𝟙 ×h N)) in
       (⊤ ⊢ ∀h ((hd_nats_s_pre N n ≡ hd_nats_z_pre N _) ⇒ ⊥)).

  Definition first_order_preorder_hyperdoctrine_nats_mono_axiom
    : UU
    := let n := π₂ (tm_var ((𝟙 ×h N) ×h N)) in
       let m := π₂ (π₁ (tm_var ((𝟙 ×h N) ×h N))) in
       (⊤ ⊢ ∀h ∀h (hd_nats_s_pre N n ≡ hd_nats_s_pre N m ⇒ n ≡ m)).

  Definition first_order_preorder_hyperdoctrine_nats_axioms
    : UU
    := first_order_preorder_hyperdoctrine_nats_zs_axiom
       ×
       first_order_preorder_hyperdoctrine_nats_mono_axiom.
End PreorderHyperdoctrineAxioms.

Definition first_order_preorder_hyperdoctrine_nats
           (H : first_order_preorder_hyperdoctrine)
  : UU
  := ∑ (N : first_order_preorder_hyperdoctrine_nats_data H),
     first_order_preorder_hyperdoctrine_nats_axioms N.

Definition make_first_order_preorder_hyperdoctrine_nats
           {H : first_order_preorder_hyperdoctrine}
           (N : first_order_preorder_hyperdoctrine_nats_data H)
           (P : first_order_preorder_hyperdoctrine_nats_axioms N)
  : first_order_preorder_hyperdoctrine_nats H
  := N ,, P.

Coercion first_order_preorder_hyperdoctrine_nats_to_data
         {H : first_order_preorder_hyperdoctrine}
         (N : first_order_preorder_hyperdoctrine_nats H)
  : first_order_preorder_hyperdoctrine_nats_data H
  := pr1 N.
