(********************************************************************************

 Reflexive Graphs

 We define reflexive graphs for the purpose of characterizing identity types.

 A reflexive graph consists of:
 - a type [A type] called vertices,
 - a family of types [a, b : A ⊢ a ≈ b type] called edges,
 - and a reflexivity datum [a : A ⊢ refl a : a ≈ a].
 A reflexive graph is univalent if edges are equivalent to identifications.

 Reflexive graphs can be combined using the combinators in [Examples.v]
 to characterize the identifications of many types.

 Contents:
 1. Reflexive graphs
 1.1. Univalence
 1.2. Fundamental Theorem of Identity Types
 2. Path operations for univalent reflexive graphs
 2.1. Induction schemes
 2.2. Edge algebra
 3. Displayed reflexive graphs
 3.1. Univalence

 Author: B. Szilvasy
 February—September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Declare Scope rxgraph.
Delimit Scope rxgraph with rxgraph.
Local Open Scope rxgraph.

Declare Scope rxgraph_spec.
Delimit Scope rxgraph_spec with rxgraph_spec.

(** ** Definition of reflexive graphs *)

Definition rxgraph := ∑ (A : UU) (edge : A -> A -> UU), ∏ a, edge a a.

Coercion rxgraph_vertex (G : rxgraph) : UU := pr1 G.

Definition edge (G : rxgraph) : G -> G -> UU := pr12 G.
Notation "a '≈{' G  '}' b" := (edge G%rxgraph_spec a b) (at level 70) : rxgraph.
Notation "a '≈' b" := (edge _ a b) (at level 70) : rxgraph.

Definition refl {G : rxgraph} : ∏ (a : G), a ≈ a := pr22 G.

Definition make_rxgraph
  (A : UU)
  (edge : A -> A -> UU)
  (refl : ∏ a, edge a a)
  : rxgraph
  := A,, edge,, refl.

Section univalence.

  (** *** Univalence *)

  Definition id_to_edge {G : rxgraph} {a b : G} : a = b -> a ≈ b.
  Proof. intro p; induction p; apply refl. Defined.

  Definition is_univalent (G : rxgraph)
    := ∏ (a b : G), isweq (λ (p : a = b), id_to_edge p).

  Lemma isaprop_is_univalent (G : rxgraph)
    : isaprop (is_univalent G).
  Proof.
    do 2 (apply impred; intro).
    apply isapropisweq.
  Qed.

  Definition univalent_rxgraph := ∑ (G : rxgraph), is_univalent G.
  Coercion univalent_rxgraph_to_rxgraph (G : univalent_rxgraph) := pr1 G.
  Coercion rxgraph_univalence (G : univalent_rxgraph)
    : is_univalent G := pr2 G.

  Definition make_univalent_rxgraph (G : rxgraph)
    (H : is_univalent G)
    : univalent_rxgraph
    := G,, H.

  Definition weq_id_to_edge {G : rxgraph}
    (H : is_univalent G)
    (a b : G) : a = b ≃ a ≈ b
    := make_weq _ (H a b).

  Definition weq_edge_to_id {G : rxgraph}
    (H : is_univalent G)
    (a b : G) : a ≈ b ≃ a = b
    := invweq (weq_id_to_edge H a b).

  Definition edge_to_id {G : rxgraph}
    (H : is_univalent G)
    {a b : G} : a ≈ b -> a = b
    := invmap (weq_id_to_edge H a b).

  Definition edges_from (G : rxgraph) (a : G) : UU := ∑ (b : G), a ≈ b.
  Definition edges_to   (G : rxgraph) (a : G) : UU := ∑ (b : G), b ≈ a.

  Definition make_edges_from {G : rxgraph} {a b : G} (e : a ≈ b) : edges_from G a := b,, e.
  Definition make_edges_to {G : rxgraph} {a b : G} (e : a ≈ b) : edges_to G b := a,, e.
  Coercion make_edges_from : edge >-> edges_from.
  Coercion make_edges_to : edge >-> edges_to.

  Definition edges_from_refl {G : rxgraph} (a : G) : edges_from G a := refl a.
  Definition edges_to_refl {G : rxgraph} (a : G) : edges_to G a := refl a.

  (** *** Fundamental Theorem of Identity Types

This is a variant of that from Egbert Rijke's "Introduction to Homotopy Type
Theory", (DOI:10.1017/9781108933568, arXiv:2212.11082).

Let [G] be a reflexive graph. The following are equivalent.
1. [G] is univalent.
2. Every [edges_from a] (or [edges_to a]) for [a : G] is a proposition.
3. Every [edges_from a] (or [edges_to a]) for [a : G] is
   contractible with centre [edges_*_refl a].

   *)

  (** 3 -> 1 *)
  Lemma is_univalent_from_iscontr_edges_from (G : rxgraph)
    (H : ∏ (a : G), iscontr (edges_from G a))
    : is_univalent G.
  Proof.
    intros a b.
    apply isweqtotaltofib; clear b.
    apply isweqcontrcontr.
    - apply iscontr_paths_from.
    - apply H.
  Defined.

  (** 2 -> 1 *)
  Lemma is_univalent_from_isaprop_edges_from (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_from G a))
    : is_univalent G.
  Proof.
    apply is_univalent_from_iscontr_edges_from.
    intro a.
    apply iscontraprop1; [|apply edges_from_refl].
    apply H.
  Defined.

  (** 1 -> 2 *)
  Lemma is_univalent_to_isaprop_edges_from (G : rxgraph)
    (H : is_univalent G)
    : ∏ (a : G), isaprop (edges_from G a).
  Proof.
    intro a.
    apply (isofhlevelweqb 1 (Y:=paths_from a)).
    - refine (make_weq _ (isweqfibtototal _ _ _)).
      intro b.
      apply weq_edge_to_id, H.
    - apply isapropifcontr, iscontr_paths_from.
  Qed. (* [isaprop] should not be used transparently *)

  (** 1 -> 3 *)
  Lemma is_univalent_to_iscontr_edges_from (G : rxgraph)
    (H : is_univalent G)
    : ∏ (a : G), iscontr (edges_from G a).
  Proof.
    intro a.
    apply iscontraprop1; [|apply edges_from_refl].
    apply is_univalent_to_isaprop_edges_from, H.
  Defined.

  (** 3 ([edges_to]) -> 3 ([edges_from]) *)
  Lemma isaprop_edges_to_implies_isaprop_edges_from (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_to G a))
    : ∏ (a : G), isaprop (edges_from G a).
  Proof.
    intro a; apply invproofirrelevance.
    intros [b₁ e₁] [b₂ e₂].
    assert (p : edges_to_refl _ = a,,e₁); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    assert (p : edges_to_refl _ = b₁,,e₂); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    reflexivity.
  Qed.

  (** 3 ([edges_from]) -> 3 ([edges_to]) *)
  Lemma isaprop_edges_from_implies_isaprop_edges_to (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_from G a))
    : ∏ (a : G), isaprop (edges_to G a).
  Proof.
    intro a; apply invproofirrelevance.
    intros [b₁ e₁] [b₂ e₂].
    assert (p : edges_from_refl _ = a,,e₁); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    assert (p : edges_from_refl _ = b₁,,e₂); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    reflexivity.
  Qed.

  (** 2 -> 1 *)
  Lemma is_univalent_from_isaprop_edges_to (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_to G a))
    : is_univalent G.
  Proof.
    use is_univalent_from_isaprop_edges_from.
    exact (isaprop_edges_to_implies_isaprop_edges_from _ H).
  Defined.

  (** 3 -> 1 *)
  Lemma is_univalent_from_iscontr_edges_to (G : rxgraph)
    (H : ∏ (a : G), iscontr (edges_to G a))
    : is_univalent G.
  Proof.
    use is_univalent_from_isaprop_edges_to.
    intro a; apply isapropifcontr, H.
  Defined.

  (** 1 -> 2 *)
  Lemma is_univalent_to_isaprop_edges_to (G : rxgraph)
    (H : is_univalent G)
    : ∏ (a : G), isaprop (edges_to G a).
  Proof.
    use isaprop_edges_from_implies_isaprop_edges_to.
    use is_univalent_to_isaprop_edges_from.
    exact H.
  Qed.

  (** 1 -> 3 *)
  Lemma is_univalent_to_iscontr_edges_to (G : rxgraph)
    (H : is_univalent G)
    : ∏ (a : G), iscontr (edges_to G a).
  Proof.
    intro a; apply iscontraprop1.
    - apply is_univalent_to_isaprop_edges_to, H.
    - apply edges_to_refl.
  Defined.

  (** A consequence is that it suffices to give an arbitrary equivalence, rather
      than needing to prove that [id_to_edge] specifically is an equivalence. *)
  Theorem is_univalent_from_weq (G : rxgraph)
    (w : ∏ (a b : G), a = b ≃ a ≈ b)
    : is_univalent G.
  Proof.
    apply is_univalent_from_iscontr_edges_from.
    intro a.
    apply (iscontrweqf (X:=paths_from a)).
    - apply weqfibtototal, w.
    - apply iscontr_paths_from.
  Qed.

End univalence.

(** ** Path operations for univalent reflexive graphs *)

Section induction.
  (** *** Induction schemes *)

  (** Unbased induction *)

  Definition rxgraph_edge_rect (G : rxgraph)
    (H : is_univalent G)
    (P : ∏ (a b : G), a ≈ b -> UU)
    (base : ∏ (a : G), P a a (refl a))
    : ∏ (a b : G) (e : a ≈ b), P a b e.
  Proof.
    intros a b e.
    refine (transportb (λ (c : edges_from G a), P a (pr1 c) (pr2 c))
              (_ : b,, e = edges_from_refl a)
              (base a)).
    exact (pr2 (is_univalent_to_iscontr_edges_from G H a) _).
  Defined.

  Definition rxgraph_edge_rect' (G : univalent_rxgraph)
    (P : ∏ (a b : G), a ≈ b -> UU)
    (base : ∏ (a : G), P a a (refl a))
    : ∏ (a b : G) (e : a ≈ b), P a b e
    := rxgraph_edge_rect G G P base.

  Definition rxgraph_edge_rect_eq (G : rxgraph)
    (H : is_univalent G)
    (P : ∏ (a b : G), a ≈ b -> UU)
    (base : ∏ (a : G), P a a (refl a))
    (a : G)
    : rxgraph_edge_rect G H P base a a (refl a) = base a.
  Proof.
    refine (maponpaths (λ p, transportb _ p (base a)) (_ : _ = idpath _)).
    apply proofirrelevancecontr, (is_univalent_to_isaprop_edges_from G H).
  Defined.

  (** Based induction *)

  Definition rxgraph_edge_rect_left (G : rxgraph)
    (H : is_univalent G)
    (a : G)
    (P : ∏ (b : G), a ≈ b -> UU)
    (base : P a (refl a))
    : ∏ (b : G) (e : a ≈ b), P b e.
  Proof.
    intros b e.
    refine (transportb (λ (c : edges_from G a), P (pr1 c) (pr2 c))
              (_ : b,, e = edges_from_refl a)
              base).
    exact (pr2 (is_univalent_to_iscontr_edges_from G H a) _).
  Defined.

  Definition rxgraph_edge_rect_left' (G : univalent_rxgraph)
    (a : G)
    (P : ∏ (b : G), a ≈ b -> UU)
    (base : P a (refl a))
    : ∏ (b : G) (e : a ≈ b), P b e
    := rxgraph_edge_rect_left G G a P base.

  Definition rxgraph_edge_rect_left_eq (G : rxgraph)
    (H : is_univalent G)
    (a : G)
    (P : ∏ (b : G), a ≈ b -> UU)
    (base : P a (refl a))
    : rxgraph_edge_rect_left G H a P base a (refl a) = base.
  Proof.
    refine (maponpaths (λ p, transportb _ p base) (_ : _ = idpath _)).
    apply proofirrelevancecontr, (is_univalent_to_isaprop_edges_from G H).
  Defined.

  Definition rxgraph_edge_rect_right (G : rxgraph)
    (H : is_univalent G)
    (b : G)
    (P : ∏ (a : G), a ≈ b -> UU)
    (base : P b (refl b))
    : ∏ (a : G) (e : a ≈ b), P a e.
  Proof.
    intros a e.
    refine (transportb (λ (c : edges_to G b), P (pr1 c) (pr2 c))
              (_ : a,, e = edges_to_refl b)
              base).
    exact (pr2 (is_univalent_to_iscontr_edges_to G H b) _).
  Defined.

  Definition rxgraph_edge_rect_right' (G : univalent_rxgraph)
    (b : G)
    (P : ∏ (a : G), a ≈ b -> UU)
    (base : P b (refl b))
    : ∏ (a : G) (e : a ≈ b), P a e
    := rxgraph_edge_rect_right G G b P base.

  Definition rxgraph_edge_rect_right_eq (G : rxgraph)
    (H : is_univalent G)
    (b : G)
    (P : ∏ (a : G), a ≈ b -> UU)
    (base : P b (refl b))
    : rxgraph_edge_rect_right G H b P base b (refl b) = base.
  Proof.
    refine (maponpaths (λ p, transportb _ p base) (_ : _ = idpath _)).
    apply proofirrelevancecontr, (is_univalent_to_isaprop_edges_to G H).
  Defined.

  (** Examples using the induction schemes with the [elim] and [induction]
      tactics. *)

  Goal ∏ (G : univalent_rxgraph) (Q : UU) (a b : G) (f : G -> Q) (e : a ≈ b), f a = f b.
  Proof.
    intros.
    Succeed elim e using rxgraph_edge_rect_left'; exact (idpath (f a)).
    Succeed revert b e; apply rxgraph_edge_rect_left'.
    Succeed induction a, e using (rxgraph_edge_rect_right' G b); exact (idpath (f b)).
    Succeed revert a b e; apply rxgraph_edge_rect'; intro a.
    induction e using rxgraph_edge_rect'.
    easy.
  Qed.

End induction.

Section algebra.
  (** *** Edge algebra *)

  Definition edge_inv {G : rxgraph} (H : is_univalent G)
    {a b : G} (e : a ≈ b) : b ≈ a.
  Proof.
    exact (rxgraph_edge_rect _ H
             (λ (a b : G) _, b ≈ a) refl a b e).
  Defined.

  Definition edge_inv_refl {G : rxgraph} (H : is_univalent G)
    (a : G) : edge_inv H (refl a) = refl a.
  Proof.
    exact (rxgraph_edge_rect_eq _ H
             (λ (a b : G) _, b ≈ a) refl a).
  Defined.

  Lemma edge_inv_edge_inv {G : rxgraph} (H : is_univalent G)
    {a b : G} (e : a ≈ b)
    : edge_inv H (edge_inv H e) = e.
  Proof.
    elim e using (rxgraph_edge_rect _ H).
    clear a b e; intro a.
    etrans; [apply maponpaths, edge_inv_refl|].
    apply edge_inv_refl.
  Defined.

  Lemma isweq_edge_inv {G : rxgraph} (H : is_univalent G)
    : ∏ (a b : G), isweq (λ (e : a ≈ b), edge_inv H e).
  Proof.
    intros a b; use isweq_iso.
    - exact (edge_inv H).
    - apply edge_inv_edge_inv.
    - apply edge_inv_edge_inv.
  Defined.

  Definition edge_comp {G : rxgraph} (H : is_univalent G)
    {a b c : G} (e : a ≈ b) : b ≈ c -> a ≈ c.
  Proof.
    exact (rxgraph_edge_rect _ H
             (λ (a b : G) _, b ≈ c -> a ≈ c)
             (λ (a : G), idfun (a ≈ c))
             a b e).
  Defined.

  Definition edge_comp_refl_left {G : rxgraph} (H : is_univalent G)
    {b c : G} (e : b ≈ c)
    : edge_comp H (refl b) e = e.
  Proof.
    exact (eqtohomot
             (rxgraph_edge_rect_eq _ H
                (λ (a b : G) _, b ≈ c -> a ≈ c)
                (λ (a : G), idfun (a ≈ c))
                b)
             e).
  Defined.

  Definition edge_comp_refl_right {G : rxgraph} (H : is_univalent G)
    {a b : G} (e : a ≈ b)
    : edge_comp H e (refl b) = e.
  Proof.
    refine (rxgraph_edge_rect _ H
              (λ (a b : G) (e : a ≈ b),
                edge_comp H e (refl b) = e)
              _ a b e).
    clear a b e; intro a.
    apply edge_comp_refl_left.
  Defined.

  Lemma isweq_edge_comp_left {G : rxgraph} (H : is_univalent G)
    {a b : G} (e : a ≈ b)
    : ∏ c, isweq (λ (e' : b ≈ c), edge_comp H e e').
  Proof.
    intro c.
    elim e using (rxgraph_edge_rect _ H).
    clear a b e; intro a.
    use isweqhomot.
    - exact (idfun _).
    - intro e.
      apply pathsinv0.
      apply edge_comp_refl_left.
    - apply idisweq.
  Qed.

  Lemma isweq_edge_comp_right {G : rxgraph} (H : is_univalent G)
    {b c : G} (e : b ≈ c)
    : ∏ a, isweq (λ (e' : a ≈ b), edge_comp H e' e).
  Proof.
    intro a.
    elim e using (rxgraph_edge_rect _ H).
    clear b c e; intro b.
    use isweqhomot.
    - exact (idfun _).
    - intro e.
      apply pathsinv0.
      apply edge_comp_refl_right.
    - apply idisweq.
  Qed.

End algebra.

(** ** Displayed reflexive graphs *)

Definition disp_rxgraph (B : rxgraph) :=
  ∑ (E : B -> UU)
    (disp_edge : ∏ (x y : B) (e : x ≈ y), E x -> E y -> UU),
    ∏ (x : B) (a : E x), disp_edge x x (refl x) a a.

Definition disp_rxgraph_vertex {B : rxgraph} (E : disp_rxgraph B)
  : B -> UU := pr1 E.
Coercion disp_rxgraph_vertex : disp_rxgraph >-> Funclass.

Definition disp_edge {B : rxgraph} (E : disp_rxgraph B)
  : ∏ {x y : B} (e : x ≈ y), E x -> E y -> UU := pr12 E.
Notation "a '≈{' E  '}[' e  ']' b" := (disp_edge E%rxgraph_spec e a b) (at level 70) : rxgraph.
Notation "a '≈[' e  ']' b" := (disp_edge _ e a b) (at level 70) : rxgraph.

Definition disp_refl {B : rxgraph} {E : disp_rxgraph B}
  : ∏ (x : B) (a : E x), a ≈[ refl x ] a := pr22 E.

Definition make_disp_rxgraph
  (B : rxgraph)
  (E : B -> UU)
  (disp_edge : ∏ (x y : B) (e : x ≈ y), E x -> E y -> UU)
  (disp_refl : ∏ (x : B) (a : E x), disp_edge x x (refl x) a a)
  : disp_rxgraph B
  := E,, disp_edge,, disp_refl.

Section univalence.
  Context {B : rxgraph}.

  (** *** Univalence

The component of a displayed reflexive graph [x : B ⊢ E[x]] over [x : B] is the
reflexive graph obtained by fixing it at [x].  A displayed reflexive graph is
(by definition) univalent if all its components are. *)

  Definition disp_rxgraph_at (E : disp_rxgraph B)
    (x : B) : rxgraph.
  Proof.
    use make_rxgraph.
    - exact (E x).
    - intros aa bb.
      exact (aa ≈[ refl x ] bb).
    - intro aa.
      exact (disp_refl x aa).
  Defined.

  Definition is_disp_univalent (E : disp_rxgraph B) : UU
    := ∏ (x : B), is_univalent (disp_rxgraph_at E x).

  Lemma isaprop_is_disp_univalent (E : disp_rxgraph B)
    : isaprop (is_disp_univalent E).
  Proof.
    apply impred; intro.
    apply isaprop_is_univalent.
  Qed.

  (** Another way to characterize displayed univalence is via [PathOver]. *)

  Definition PathOver_to_disp_edge (E : disp_rxgraph B)
    {x y : B} (e : x = y) (a : E x) (b : E y)
    : PathOver e a b -> a ≈[ id_to_edge e ] b.
  Proof.
    intro p.
    induction e; induction p.
    apply disp_refl.
  Defined.

  Definition is_disp_univalent_alt (E : disp_rxgraph B) : UU
    := ∏ (x y : B) (e : x = y) (a : E x) (b : E y),
      isweq (PathOver_to_disp_edge E e a b).

  Lemma isaprop_is_disp_univalent_alt (E : disp_rxgraph B)
    : isaprop (is_disp_univalent_alt E).
  Proof.
    do 5 (apply impred; intro).
    apply isapropisweq.
  Qed.

  Lemma weq_is_disp_univalent_alt (E : disp_rxgraph B)
    : is_disp_univalent E ≃ is_disp_univalent_alt E.
  Proof.
    use weqimplimpl.
    - intros H x y e.
      induction e; exact (H x).
    - intros H x.
      exact (H x x (idpath x)).
    - apply isaprop_is_disp_univalent.
    - apply isaprop_is_disp_univalent_alt.
  Qed.

  Definition weq_PathOver_to_disp_edge {E : disp_rxgraph B}
    (HE : is_disp_univalent E)
    {x y : B} (e : x = y) (a : E x) (b : E y)
    : PathOver e a b ≃ a ≈[ id_to_edge e ] b.
  Proof.
    apply (make_weq (PathOver_to_disp_edge E e a b)).
    apply (weq_is_disp_univalent_alt E HE).
  Defined.

  Definition weq_PathOver_to_disp_edge' {E : disp_rxgraph B}
    (HB : is_univalent B) (HE : is_disp_univalent E)
    {x y : B} (e : x ≈ y) (a : E x) (b : E y)
    : PathOver (edge_to_id HB e) a b ≃ a ≈[ e ] b.
  Proof.
    intermediate_weq (a ≈[ id_to_edge (edge_to_id HB e) ] b).
    { apply (weq_PathOver_to_disp_edge HE). }
    refine (transportf (λ e', a ≈[e'] b ≃ a ≈[e] b) _ (idweq _)).
    exact (homotinvweqweq0 (weq_edge_to_id HB x y) _).
  Defined.

End univalence.

Definition univalent_disp_rxgraph (B : rxgraph)
  := ∑ (E : disp_rxgraph B), is_disp_univalent E.
Coercion univalent_disp_rxgraph_to_disp_rxgraph
  {B : rxgraph} (E : univalent_disp_rxgraph B)
  : disp_rxgraph B := pr1 E.
Coercion disp_rxgraph_univalence
  {B : rxgraph} (E : univalent_disp_rxgraph B)
  : is_disp_univalent E := pr2 E.

Definition make_univalent_disp_rxgraph
  {B : rxgraph} (E : disp_rxgraph B)
  (H : is_disp_univalent E)
  : univalent_disp_rxgraph B
  := E,, H.
