(********************************************************************************

 Fibred Reflexive Graphs

 The work here is based on Jon Sterling, 2026, "Reflexive graph lenses in
 Univalent Foundations" (doi:10.1017/S0960129526100565, arXiv:2404.07854).

 Contents:
 1. Definitions
 2. Relationship with lenses
 2.1. Pushforwards and pullbacks
 2.2. Straightening of edges
 2.3. Lenses from fibrations
 2.4. Equivalence between fibrations and lenses

 Author: B. Szilvasy
 September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.
Require Import UniMath.IdentitySystems.Lenses.
Require Import UniMath.IdentitySystems.RXGraphOfRXGraphs.

Local Open Scope rxgraph.

(** ** Definitions *)

(** Covariant fibrations *)

Definition is_covy_fibration
  {B : rxgraph} (E : disp_rxgraph B)
  := ∏ (x y : B) (e : x ≈ y) (a : E x),
    ∃! (b : E y), a ≈[e] b.
Definition covy_fibration (B : rxgraph) : UU :=
  ∑ (E : disp_rxgraph B), is_covy_fibration E.

Lemma isaprop_is_covy_fibration
  {B : rxgraph} (E : disp_rxgraph B)
  : isaprop (is_covy_fibration E).
Proof.
  do 4 (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma is_univalent_covy_fibration {B : rxgraph}
  (E : disp_rxgraph B) (H : is_covy_fibration E)
  : is_disp_univalent E.
Proof.
  intro x; apply is_univalent_from_iscontr_edges_from.
  exact (H x x (refl x)).
Defined.

Coercion covy_fibration_to_disp_rxgraph {B : rxgraph} (E : covy_fibration B)
  : univalent_disp_rxgraph B
  := make_univalent_disp_rxgraph (pr1 E)
       (is_univalent_covy_fibration (pr1 E) (pr2 E)).
Coercion covy_fibration_property {B : rxgraph} (E : covy_fibration B)
  : is_covy_fibration E := pr2 E.

Definition covy_fibration_lift
  {B : rxgraph} {E : disp_rxgraph B}
  (ℓ : is_covy_fibration E)
  : ∏ {x y : B} (e : x ≈ y) (a : E x),
    ∃! (b : E y), a ≈[e] b
  := ℓ.

(** Contravariant fibrations *)

Definition is_contra_fibration
  {B : rxgraph} (E : disp_rxgraph B)
  := ∏ (x y : B) (e : x ≈ y) (b : E y),
    ∃! (a : E x), a ≈[e] b.
Definition contra_fibration (B : rxgraph) : UU :=
  ∑ (E : disp_rxgraph B), is_contra_fibration E.

Lemma isaprop_is_contra_fibration
  {B : rxgraph} (E : disp_rxgraph B)
  : isaprop (is_contra_fibration E).
Proof.
  do 4 (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma is_univalent_contra_fibration {B : rxgraph}
  (E : disp_rxgraph B) (H : is_contra_fibration E)
  : is_disp_univalent E.
Proof.
  intro x; apply is_univalent_from_iscontr_edges_to.
  exact (H x x (refl x)).
Defined.

Coercion contra_fibration_to_disp_rxgraph {B : rxgraph} (E : contra_fibration B)
  : univalent_disp_rxgraph B
  := make_univalent_disp_rxgraph (pr1 E)
       (is_univalent_contra_fibration (pr1 E) (pr2 E)).
Coercion contra_fibration_property {B : rxgraph} (E : contra_fibration B)
  : is_contra_fibration E := pr2 E.

Definition contra_fibration_lift
  {B : rxgraph} {E : disp_rxgraph B}
  (ℓ : is_contra_fibration E)
  : ∏ {x y : B} (e : x ≈ y) (b : E y),
    ∃! (a : E x), a ≈[e] b
  := ℓ.

(** ** Relationship with lenses *)

(** *** Pushforwards and pullbacks *)

(** Pushforwards *)

Definition pushforwards_are_universal {B : rxgraph} (E : covy_lens B) : UU
  := ∏ (x y : B) (e : x ≈ y) (a : E x),
    isaprop (edges_from (E y) (lens_push E e a)).

Lemma is_covy_fibration_covy_lens {B : rxgraph} (E : covy_lens B)
  (H : pushforwards_are_universal E)
  : is_covy_fibration (covy_lens_disp_rxgraph E).
Proof.
  intros x y e a.
  apply (iscontraprop1 (H x y e a)).
  apply edges_from_refl.
Defined.

Lemma covy_lens_pushfowards_are_universal_from_univalent
  {B : rxgraph} (E : covy_lens B)
  (HE : ∏ x, is_univalent (E x))
  : pushforwards_are_universal E.
Proof.
  intros x y e a.
  apply is_univalent_to_isaprop_edges_from, HE.
Qed.

Lemma covy_lens_univalent_from_pushforwards_are_universal
  {B : rxgraph} (E : covy_lens B)
  (H : pushforwards_are_universal E)
  : ∏ x, is_univalent (E x).
Proof.
  intro x; apply is_univalent_from_isaprop_edges_from; intro a.
  apply (isofhlevelweqf 1 (X:=edges_from _ (lens_push E (refl x) a))).
  - apply weqfibtototal; intro b.
    refine (transportb (λ c, c ≈ b ≃ a ≈ b) _ (idweq _)).
    refine (base_paths (edges_from_refl _) (a,, lens_push_refl E x a) _).
    apply proofirrelevance, H.
  - apply H.
Qed.

Definition covy_fibration_from_univalent_covy_lens {B : rxgraph}
  (E : univalent_covy_lens B)
  : covy_fibration B.
Proof.
  exists (covy_lens_disp_rxgraph E).
  apply is_covy_fibration_covy_lens, covy_lens_pushfowards_are_universal_from_univalent.
  intro x.
  apply rxgraph_univalence.
Defined.

(** Pullbacks *)

Definition pullbacks_are_universal {B : rxgraph} (E : contra_lens B) : UU
  := ∏ (x y : B) (e : x ≈ y) (a : E y),
    isaprop (edges_to (E x) (lens_pull E e a)).

Lemma is_contra_fibration_contra_lens {B : rxgraph} (E : contra_lens B)
  (H : pullbacks_are_universal E)
  : is_contra_fibration (contra_lens_disp_rxgraph E).
Proof.
  intros x y e a.
  apply (iscontraprop1 (H x y e a)).
  apply edges_to_refl.
Defined.

Lemma contra_lens_pullfowards_are_universal_from_univalent
  {B : rxgraph} (E : contra_lens B)
  (HE : ∏ x, is_univalent (E x))
  : pullbacks_are_universal E.
Proof.
  intros x y e a.
  apply is_univalent_to_isaprop_edges_to, HE.
Qed.

Lemma contra_lens_univalent_from_pullbacks_are_universal
  {B : rxgraph} (E : contra_lens B)
  (H : pullbacks_are_universal E)
  : ∏ x, is_univalent (E x).
Proof.
  intro x; apply is_univalent_from_isaprop_edges_to; intro b.
  apply (isofhlevelweqf 1 (X:=edges_to _ (lens_pull E (refl x) b))).
  - apply weqfibtototal; intro a.
    refine (transportb (λ c, a ≈ c ≃ a ≈ b) _ (idweq _)).
    refine (base_paths (edges_to_refl _) (b,, lens_pull_refl E x b) _).
    apply proofirrelevance, H.
  - apply H.
Qed.

Definition contra_fibration_from_univalent_contra_lens {B : rxgraph}
  (E : univalent_contra_lens B)
  : contra_fibration B.
Proof.
  exists (contra_lens_disp_rxgraph E).
  apply is_contra_fibration_contra_lens, contra_lens_pullfowards_are_universal_from_univalent.
  intro x.
  apply rxgraph_univalence.
Defined.

(** *** Straightening of edges *)

Section covy_straightening.
  Context {B : rxgraph} (E : covy_fibration B)
    {x y : B} (e : x ≈ y) {a : E x}.

  Let p := iscontrpr1 (covy_fibration_lift E e a).
  Local Notation "'p*a'" := (pr1 p).
  Local Notation "'p†a'" := (pr2 p).

  Definition covy_edge_str₀
    {b : E y} (e' : a ≈[e] b)
    (H : p = b,, e')
    : p*a ≈{E⟦y⟧} b.
  Proof.
    refine (transportb (λ c, pr1 c ≈{E⟦y⟧} pr1 (b,, e')) H _).
    apply refl.
  Defined.

  Definition covy_edge_str
    {b : E y} (e' : a ≈[e] b)
    : p*a ≈{E⟦y⟧} b.
  Proof.
    apply (covy_edge_str₀ e').
    apply pathsinv0, iscontr_uniqueness.
  Defined.

  Definition covy_edge_unstr₀
    {b : E y} (e' : p*a ≈{E⟦y⟧} b)
    (I : edges_from_refl (G:=E⟦y⟧) p*a = b,, e')
    : a ≈[e] b.
  Proof.
    refine (transportf (λ c, a ≈[e] pr1 c) I _).
    exact p†a.
  Defined.

  Definition covy_edge_unstr
    {b : E y} (e' : p*a ≈{E⟦y⟧} b)
    : a ≈[e] b.
  Proof.
    apply (covy_edge_unstr₀ e').
    apply proofirrelevance, (is_univalent_to_isaprop_edges_from (E⟦y⟧)).
    apply is_univalent_covy_fibration, E.
  Defined.

  Definition covy_edge_str₀_after_unstr₀
    {b : E y} (e' : p*a ≈{E⟦y⟧} b)
    (I : edges_from_refl (G:=E⟦y⟧) p*a = b,, e')
    (H : p = b,, covy_edge_unstr₀ e' I)
    : covy_edge_str₀ (covy_edge_unstr₀ e' I) H = e'.
  Proof.
    pose (be' := b,, e' : ∑ b, p*a ≈{E⟦y⟧} b).
    fold be' in I; fold (pr1 be') (pr2 be') in H |- *.
    induction I; clear b e'.
    cbn in H |- *.
    assert (H' : idpath p = H).
    { apply proofirrelevancecontr.
      refine ((_ : isaprop _) _ _).
      apply isapropifcontr, covy_fibration_lift, E. }
    induction H'.
    reflexivity.
  Qed.

  Definition covy_edge_unstr₀_after_str₀
    {b : E y} (e' : a ≈[e] b)
    (H : p = b,, e')
    (I : edges_from_refl (G:=E⟦y⟧) p*a = b,, covy_edge_str₀ e' H)
    : covy_edge_unstr₀ (covy_edge_str₀ e' H) I = e'.
  Proof.
    pose (be' := b,, e' : ∑ b, a ≈[e] b).
    fold be' in H; fold (pr1 be') (pr2 be') in I |- *.
    induction H; clear b e'.
    cbn in I |- *.
    assert (I' : idpath _ = I).
    { apply proofirrelevancecontr.
      refine ((_ : isaprop _) _ _).
      apply isapropifcontr, covy_fibration_lift, E. }
    induction I'.
    reflexivity.
  Qed.

  Corollary isweq_covy_edge_str (b : E y)
    : isweq (λ (e' : a ≈[e] b), covy_edge_str e').
  Proof.
    use isweq_iso.
    - exact covy_edge_unstr.
    - intro e'; apply covy_edge_unstr₀_after_str₀.
    - intro e'; apply covy_edge_str₀_after_unstr₀.
  Defined.

  Definition weq_covy_edge_str (b : E y)
    : a ≈[ e ] b ≃ p*a ≈{E⟦y⟧} b
    := make_weq _ (isweq_covy_edge_str b).

  Definition weq_covy_edge_unstr (b : E y)
    : p*a ≈{E⟦y⟧} b ≃ a ≈[ e ] b
    := invweq (weq_covy_edge_str b).

End covy_straightening.
Arguments weq_covy_edge_str {B} E {x y} e a b.
Arguments weq_covy_edge_unstr {B} E {x y} e a b.

Section contra_straightening.
  Context {B : rxgraph} (E : contra_fibration B)
    {x y : B} (e : x ≈ y) {b : E y}.

  Let p := iscontrpr1 (contra_fibration_lift E e b).
  Local Notation "'p*b'" := (pr1 p).
  Local Notation "'p†b'" := (pr2 p).

  Definition contra_edge_str₀
    {a : E x} (e' : a ≈[e] b)
    (H : p = a,, e')
    : a ≈{E⟦x⟧} p*b.
  Proof.
    refine (transportb (λ c, pr1 (a,, e' : ∑ a, a ≈[e] b) ≈{E⟦x⟧} pr1 c) H _).
    apply refl.
  Defined.

  Definition contra_edge_str
    {a : E x} (e' : a ≈[e] b)
    : a ≈{E⟦x⟧} p*b.
  Proof.
    apply (contra_edge_str₀ e').
    apply pathsinv0, iscontr_uniqueness.
  Defined.

  Definition contra_edge_unstr₀
    {a : E x} (e' : a ≈{E⟦x⟧} p*b)
    (I : edges_to_refl (G:=E⟦x⟧) p*b = a,, e')
    : a ≈[e] b.
  Proof.
    refine (transportf (λ c, pr1 c ≈[e] b) I _).
    exact p†b.
  Defined.

  Definition contra_edge_unstr
    {a : E x} (e' : a ≈{E⟦x⟧} p*b)
    : a ≈[e] b.
  Proof.
    apply (contra_edge_unstr₀ e').
    apply proofirrelevance, (is_univalent_to_isaprop_edges_to (E⟦x⟧)).
    apply is_univalent_contra_fibration, E.
  Defined.

  Definition contra_edge_str₀_after_unstr₀
    {a : E x} (e' : a ≈{E⟦x⟧} p*b)
    (I : edges_to_refl (G:=E⟦x⟧) p*b = a,, e')
    (H : p = a,, contra_edge_unstr₀ e' I)
    : contra_edge_str₀ (contra_edge_unstr₀ e' I) H = e'.
  Proof.
    pose (ae' := a,, e' : ∑ a, a ≈{E⟦x⟧} p*b).
    fold ae' in I; fold (pr1 ae') (pr2 ae') in H |- *.
    induction I; clear a e'.
    cbn in H |- *.
    assert (H' : idpath p = H).
    { apply proofirrelevancecontr.
      refine ((_ : isaprop _) _ _).
      apply isapropifcontr, contra_fibration_lift, E. }
    induction H'.
    reflexivity.
  Qed.

  Definition contra_edge_unstr₀_after_str₀
    {a : E x} (e' : a ≈[e] b)
    (H : p = a,, e')
    (I : edges_to_refl (G:=E⟦x⟧) p*b = a,, contra_edge_str₀ e' H)
    : contra_edge_unstr₀ (contra_edge_str₀ e' H) I = e'.
  Proof.
    pose (ae' := a,, e' : ∑ a, a ≈[e] b).
    fold ae' in H; fold (pr1 ae') (pr2 ae') in I |- *.
    induction H; clear a e'.
    cbn in I |- *.
    assert (I' : idpath _ = I).
    { apply proofirrelevancecontr.
      refine ((_ : isaprop _) _ _).
      apply isapropifcontr, contra_fibration_lift, E. }
    induction I'.
    reflexivity.
  Qed.

  Corollary isweq_contra_edge_str (a : E x)
    : isweq (λ (e' : a ≈[e] b), contra_edge_str e').
  Proof.
    use isweq_iso.
    - exact contra_edge_unstr.
    - intro e'; apply contra_edge_unstr₀_after_str₀.
    - intro e'; apply contra_edge_str₀_after_unstr₀.
  Defined.

  Definition weq_contra_edge_str (a : E x)
    : a ≈[ e ] b ≃ a ≈{E⟦x⟧} p*b
    := make_weq _ (isweq_contra_edge_str a).

  Definition weq_contra_edge_unstr (a : E x)
    : a ≈{E⟦x⟧} p*b ≃ a ≈[ e ] b
    := invweq (weq_contra_edge_str a).

End contra_straightening.
Arguments weq_contra_edge_str {B} E {x y} e b a.
Arguments weq_contra_edge_unstr {B} E {x y} e b a.

(** *** Lenses from fibrations *)

Definition univalent_covy_lens_from_fibration {B : rxgraph}
  (E : covy_fibration B)
  : univalent_covy_lens B.
Proof.
  use make_univalent_covy_lens.
  - intro x; exists (E⟦x⟧).
    apply is_univalent_covy_fibration, E.
  - intros x y e a.
    exact (pr1 (iscontrpr1 (covy_fibration_lift E e a))).
  - intros x a.
    refine (weq_covy_edge_str E (refl x) a a _).
    exact (disp_refl x a).
Defined.

Definition univalent_contra_lens_from_fibration {B : rxgraph}
  (E : contra_fibration B)
  : univalent_contra_lens B.
Proof.
  use make_univalent_contra_lens.
  - intro x; exists (E⟦x⟧).
    apply is_univalent_contra_fibration, E.
  - intros x y e a.
    exact (pr1 (iscontrpr1 (contra_fibration_lift E e a))).
  - intros x a.
    refine (weq_contra_edge_str E (refl x) a a _).
    exact (disp_refl x a).
Defined.

(** *** Equivalence between fibrations and lenses

 We do not yet show that the round-trip below
 preserves the lens structure itself.
 *)

Definition disp_rxgraph_from_covy_lens_from_fibration_iso
  {B : rxgraph} (E : covy_fibration B)
  : disp_rxgraph_iso E
      (covy_lens_disp_rxgraph (univalent_covy_lens_from_fibration E)).
Proof.
  use make_disp_rxgraph_iso.
  - intros x; exact (idweq (E x)).
  - intros x y e a b; cbn in a, b |- *.
    exact (weq_covy_edge_str E e a b).
  - easy.
Defined.

Definition covy_lens_from_fibration_from_covy_lens_iso
  {B : rxgraph} (E : univalent_covy_lens B)
  : ∏ (x : B),
    rxgraph_iso
      (E x)
      (univalent_covy_lens_from_fibration
         (covy_fibration_from_univalent_covy_lens E)
         x).
Proof.
  intro x.
  use make_rxgraph_iso.
  - exact (idweq (E x)).
  - intros a b; cbn in a, b |- *.
    eexists.
    apply (isweq_edge_comp_left (E x) (lens_push_refl E x a)).
  - intros a; cbn in a |- *.
    apply edge_comp_refl_right.
Defined.

Definition disp_rxgraph_from_contra_lens_from_fibration_iso
  {B : rxgraph} (E : contra_fibration B)
  : disp_rxgraph_iso E
      (contra_lens_disp_rxgraph (univalent_contra_lens_from_fibration E)).
Proof.
  use make_disp_rxgraph_iso.
  - intros x; exact (idweq (E x)).
  - intros x y e a b; cbn in a, b |- *.
    exact (weq_contra_edge_str E e b a).
  - easy.
Defined.

Definition contra_lens_from_fibration_from_contra_lens_iso
  {B : rxgraph} (E : univalent_contra_lens B)
  : ∏ (x : B),
    rxgraph_iso
      (E x)
      (univalent_contra_lens_from_fibration
         (contra_fibration_from_univalent_contra_lens E)
         x).
Proof.
  intro x.
  use make_rxgraph_iso.
  - exact (idweq (E x)).
  - intros a b; cbn in a, b |- *.
    eexists.
    apply (isweq_edge_comp_right (E x) (lens_pull_refl E x b)).
  - intros a; cbn in a |- *.
    apply edge_comp_refl_left.
Defined.
