(********************************************************************************

 Reflexive Graph Lenses

 Reflexive graph lenses characterize transport over the edges of a base
 reflexive graph, to construct a new displayed reflexive graph out of a family
 of reflexive graphs.  The work here is based on Jon Sterling, 2026, "Reflexive
 graph lenses in Univalent Foundations" (doi:10.1017/S0960129526100565,
 arXiv:2404.07854).

 Contents:
 1. Definitions
 1.1. Oplax covariant lenses
 1.2. Lax contravariant lenses
 1.3. Unbiased dependent lenses
 2. Definitional lenses

 Author: B. Szilvasy
 September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.

Local Open Scope rxgraph.

(** ** Definitions *)

(** *** Oplax covariant lenses

    ("covariant" because of the direction of [lens_push],
    "oplax" because of the direction of [lens_push_refl])
 *)

Definition covy_lens_structure {B : rxgraph} (E : B -> rxgraph) : UU
  := ∑ (push : ∏ (x y : B) (e : x ≈ y), E x -> E y),
    ∏ (x : B) (a : E x), push x x (refl x) a ≈ a.
Definition covy_lens (B : rxgraph) : UU
  := ∑ (E : B -> rxgraph), covy_lens_structure E.

Definition covy_lens_rxgraph {B : rxgraph} (E : covy_lens B) := pr1 E.
Coercion covy_lens_rxgraph : covy_lens >-> Funclass.
Coercion covy_lens_to_structure {B : rxgraph} (E : covy_lens B)
  : covy_lens_structure E := pr2 E.

Definition univalent_covy_lens (B : rxgraph) : UU
  := ∑ (E : B -> univalent_rxgraph), covy_lens_structure E.
Definition univalent_covy_lens_rxgraph {B : rxgraph} (E : univalent_covy_lens B) := pr1 E.
(* (Ambiguous) Coercion univalent_covy_lens_rxgraph : univalent_covy_lens >-> Funclass. *)
Coercion univalent_covy_lens_to_covy_lens {B : rxgraph}
  (E : univalent_covy_lens B) : covy_lens B
  := (univalent_rxgraph_to_rxgraph ∘ pr1 E),, pr2 E.

Definition lens_push {B : rxgraph} {E : B -> rxgraph} (ℓ : covy_lens_structure E)
  : ∏ {x y : B} (e : x ≈ y), E x -> E y := pr1 ℓ.
Definition lens_push_refl {B : rxgraph} {E : B -> rxgraph} (ℓ : covy_lens_structure E)
  : ∏ (x : B) (a : E x), lens_push ℓ (refl x) a ≈ a := pr2 ℓ.

Definition make_covy_lens_structure (B : rxgraph) (E : B -> rxgraph)
  (push : ∏ (x y : B) (e : x ≈ y), E x -> E y)
  (push_refl : ∏ (x : B) (a : E x), push x x (refl x) a ≈ a)
  : covy_lens_structure E
  := push,, push_refl.

Definition make_covy_lens (B : rxgraph) (E : B -> rxgraph)
  (push : ∏ (x y : B) (e : x ≈ y), E x -> E y)
  (push_refl : ∏ (x : B) (a : E x), push x x (refl x) a ≈ a)
  : covy_lens B
  := E,, push,, push_refl.

Definition make_univalent_covy_lens (B : rxgraph) (E : B -> univalent_rxgraph)
  (push : ∏ (x y : B) (e : x ≈ y), E x -> E y)
  (push_refl : ∏ (x : B) (a : E x), push x x (refl x) a ≈ a)
  : univalent_covy_lens B
  := E,, push,, push_refl.

Definition make_univalent_covy_lens' (B : rxgraph)
  (E : covy_lens B)
  (H : ∏ x, is_univalent (E x))
  : univalent_covy_lens B
  := make_univalent_covy_lens B
       (λ x, make_univalent_rxgraph (E x) (H x))
       (@lens_push _ _ E)
       (@lens_push_refl _ _ E).

Definition covy_lens_disp_rxgraph {B : rxgraph}
  (E : covy_lens B) : disp_rxgraph B.
Proof.
  use make_disp_rxgraph.
  - intro x; exact (E x).
  - intros x y e a b.
    exact (lens_push E e a ≈ b).
  - intros x a.
    exact (lens_push_refl E x a).
Defined.

Notation "'disp+'" := covy_lens_disp_rxgraph : rxgraph.

Lemma is_univalent_covy_lens_disp_rxgraph
  {B : rxgraph} (E : covy_lens B)
  (HE : ∏ x, is_univalent (E x))
  : is_disp_univalent (disp+ E).
Proof.
  intros x.
  apply is_univalent_from_isaprop_edges_from; intro a.
  apply (is_univalent_to_isaprop_edges_from _ (HE x)).
Defined.

Lemma weq_sec_over_contr_total2
  {A : UU} {B : A -> UU}
  (H : iscontr (∑ a, B a))
  (c := iscontrpr1 H)
  (C : ∏ a, B a -> UU)
  : (∏ (a : A) (b : B a), C a b) ≃ C (pr1 c) (pr2 c).
Proof.
  intermediate_weq (∏ (ab : ∑ a, B a), C (pr1 ab) (pr2 ab)).
  - apply invweq, weqsecovertotal2.
  - exact (weqsecovercontr _ H).
Defined.

Lemma iscontr_covy_lens_structure_over_univalent
  {B : rxgraph} (E : B -> rxgraph)
  (HB : is_univalent B)
  (HE : ∏ x, is_univalent (E x))
  : iscontr (covy_lens_structure E).
Proof.
  eapply (isofhlevelweqf 0).
  { exact (sec_total2_distributivity
             (λ x push, ∏ (a : E x), push x (refl x) a ≈ a)). }
  apply impred; intro x.
  apply (isofhlevelweqb 0 (Y:=∑ (ϕ : E x -> E x), ∏ a, ϕ a ≈ a)). {
    use weqbandf; [apply (weq_sec_over_contr_total2 (is_univalent_to_iscontr_edges_from _ HB x))|].
    intro; exact (idweq _).
  }
  change (iscontr (edges_to (E x ~> E x) (idfun _))).
  apply is_univalent_to_iscontr_edges_to.
  apply is_univalent_product_rxgraph; intro.
  apply HE.
Qed.

(** *** Lax contravariant lenses

    ("contravariant" because of the direction of [lens_pull],
    "lax" because of the direction of [lens_pull_refl])
 *)

Definition contra_lens_structure {B : rxgraph} (E : B -> rxgraph)
  := ∑ (pull : ∏ (x y : B) (e : x ≈ y), E y -> E x),
    ∏ (x : B) (a : E x), a ≈ pull x x (refl x) a.
Definition contra_lens (B : rxgraph) : UU
  := ∑ (E : B -> rxgraph), contra_lens_structure E.

Definition contra_lens_rxgraph {B : rxgraph} (E : contra_lens B) := pr1 E.
Coercion contra_lens_rxgraph : contra_lens >-> Funclass.
Coercion contra_lens_to_structure {B : rxgraph} (E : contra_lens B)
  : contra_lens_structure E := pr2 E.

Definition univalent_contra_lens (B : rxgraph) : UU
  := ∑ (E : B -> univalent_rxgraph), contra_lens_structure E.
Definition univalent_contra_lens_rxgraph {B : rxgraph} (E : univalent_contra_lens B) := pr1 E.
(* (Ambiguous) Coercion univalent_contra_lens_rxgraph : univalent_contra_lens >-> Funclass. *)
Coercion univalent_contra_lens_to_contra_lens {B : rxgraph}
  (E : univalent_contra_lens B) : contra_lens B
  := (univalent_rxgraph_to_rxgraph ∘ pr1 E),, pr2 E.

Definition lens_pull {B : rxgraph} {E : B -> rxgraph} (ℓ : contra_lens_structure E)
  : ∏ {x y : B} (e : x ≈ y), E y -> E x := pr1 ℓ.
Definition lens_pull_refl {B : rxgraph} {E : B -> rxgraph} (ℓ : contra_lens_structure E)
  : ∏ (x : B) (a : E x), a ≈ lens_pull ℓ (refl x) a := pr2 ℓ.

Definition make_contra_lens_structure (B : rxgraph) (E : B -> rxgraph)
  (pull : ∏ (x y : B) (e : x ≈ y), E y -> E x)
  (pull_refl : ∏ (x : B) (a : E x), a ≈ pull x x (refl x) a)
  : contra_lens_structure E
  := pull,, pull_refl.

Definition make_contra_lens (B : rxgraph) (E : B -> rxgraph)
  (pull : ∏ (x y : B) (e : x ≈ y), E y -> E x)
  (pull_refl : ∏ (x : B) (a : E x), a ≈ pull x x (refl x) a)
  : contra_lens B
  := E,, pull,, pull_refl.

Definition make_univalent_contra_lens (B : rxgraph) (E : B -> univalent_rxgraph)
  (pull : ∏ (x y : B) (e : x ≈ y), E y -> E x)
  (pull_refl : ∏ (x : B) (a : E x), a ≈ pull x x (refl x) a)
  : univalent_contra_lens B
  := E,, pull,, pull_refl.

Definition make_univalent_contra_lens' (B : rxgraph)
  (E : contra_lens B)
  (H : ∏ x, is_univalent (E x))
  : univalent_contra_lens B
  := make_univalent_contra_lens B
       (λ x, make_univalent_rxgraph (E x) (H x))
       (@lens_pull _ _ E)
       (@lens_pull_refl _ _ E).

Definition contra_lens_disp_rxgraph {B : rxgraph}
  (E : contra_lens B) : disp_rxgraph B.
Proof.
  use make_disp_rxgraph.
  - intro x; exact (E x).
  - intros x y e a b.
    exact (a ≈ lens_pull E e b).
  - intros x a.
    exact (lens_pull_refl E x a).
Defined.

Notation "'disp-'" := contra_lens_disp_rxgraph : rxgraph.

Lemma is_univalent_contra_lens_disp_rxgraph
  {B : rxgraph} (E : contra_lens B)
  (HE : ∏ x, is_univalent (E x))
  : is_disp_univalent (disp- E).
Proof.
  intros x.
  apply is_univalent_from_isaprop_edges_to; intro a.
  apply (is_univalent_to_isaprop_edges_to _ (HE x)).
Defined.

Lemma iscontr_contra_lens_structure_over_univalent
  {B : rxgraph} (E : B -> rxgraph)
  (HB : is_univalent B)
  (HE : ∏ x, is_univalent (E x))
  : iscontr (contra_lens_structure E).
Proof.
  eapply (isofhlevelweqf 0).
  { exact (sec_total2_distributivity
             (λ x pull, ∏ (a : E x), a ≈ pull x (refl x) a)). }
  apply impred; intro x.
  apply (isofhlevelweqb 0 (Y:=∑ (ϕ : E x -> E x), ∏ a, a ≈ ϕ a)). {
    use weqbandf; [apply (weq_sec_over_contr_total2 (is_univalent_to_iscontr_edges_from _ HB x))|].
    intro; exact (idweq _).
  }
  change (iscontr (edges_from (E x ~> E x) (idfun _))).
  apply is_univalent_to_iscontr_edges_from.
  apply is_univalent_product_rxgraph; intro.
  apply HE.
Qed.

(** Involution *)

Definition covy_to_contra_lens {B : rxgraph}
  (E : covy_lens B) : contra_lens B^op.
Proof.
  use make_contra_lens.
  - intro x; exact (E x)^op.
  - intros x y e; exact (lens_push E e).
  - intros x a; exact (lens_push_refl E x a).
Defined.

Definition contra_to_covy_lens {B : rxgraph}
  (E : contra_lens B) : covy_lens B^op.
Proof.
  use make_covy_lens.
  - intro x; exact (E x)^op.
  - intros x y e; exact (lens_pull E e).
  - intros x a; exact (lens_pull_refl E x a).
Defined.

Definition contra_to_covy_lens_involution_compute {B : rxgraph} (E : covy_lens B)
  : contra_to_covy_lens (covy_to_contra_lens E) = E.
Proof. reflexivity. Defined.

Definition covy_to_contra_lens_involution_compute {B : rxgraph} (E : contra_lens B)
  : covy_to_contra_lens (contra_to_covy_lens E) = E.
Proof. reflexivity. Defined.

Definition covy_to_contra_lens_disp_rxgraph_compute {B : rxgraph} (E : covy_lens B)
  : disp- (covy_to_contra_lens E) = (disp+ E)^op*.
Proof. reflexivity. Defined.

Definition contra_to_covy_lens_disp_rxgraph_compute {B : rxgraph} (E : contra_lens B)
  : disp+ (contra_to_covy_lens E) = (disp- E)^op*.
Proof. reflexivity. Defined.

(** *** Unbiased dependent lenses *)

Definition unbiased_lens_structure {B : rxgraph}
  (E : ∏ {a b : B}, a ≈ b -> rxgraph) : UU
  := ∑ (lext : ∏ {x y : B} (e : x ≈ y) (a : E (refl x)), E e)
       (rext : ∏ {x y : B} (e : x ≈ y) (a : E (refl y)), E e),
    (∏ (x : B) (a : E (refl x)), lext (refl x) a ≈ rext (refl x) a) ×
    (∏ (x : B) (a : E (refl x)), a ≈ rext (refl x) a).

Definition unbiased_lens (B : rxgraph) : UU
  := ∑ (E : ∏ {a b : B}, a ≈ b -> rxgraph),
    unbiased_lens_structure (@E).

Definition make_unbiased_lens_structure {B : rxgraph}
  (E : ∏ {a b : B}, a ≈ b -> rxgraph)
  (lext : ∏ {x y : B} (e : x ≈ y) (a : E (refl x)), E e)
  (rext : ∏ {x y : B} (e : x ≈ y) (a : E (refl y)), E e)
  (ext_refl : ∏ (x : B) (a : E (refl x)), lext (refl x) a ≈ rext (refl x) a)
  (rext_refl : ∏ (x : B) (a : E (refl x)), a ≈ rext (refl x) a)
  : unbiased_lens_structure (@E)
  := @lext,, @rext,, @ext_refl,, @rext_refl.

Definition make_unbiased_lens {B : rxgraph}
  (E : ∏ {a b : B}, a ≈ b -> rxgraph)
  (lext : ∏ {x y : B} (e : x ≈ y) (a : E (refl x)), E e)
  (rext : ∏ {x y : B} (e : x ≈ y) (a : E (refl y)), E e)
  (ext_refl : ∏ (x : B) (a : E (refl x)), lext (refl x) a ≈ rext (refl x) a)
  (rext_refl : ∏ (x : B) (a : E (refl x)), a ≈ rext (refl x) a)
  : unbiased_lens B
  := @E,, @lext,, @rext,, @ext_refl,, @rext_refl.

Definition unbiased_lens_family {B : rxgraph} (E : unbiased_lens B)
  : ∏ {a b : B}, a ≈ b -> rxgraph := pr1 E.
Coercion unbiased_lens_family : unbiased_lens >-> Funclass.
Coercion unbiased_lens_to_structure {B : rxgraph} (E : unbiased_lens B)
  : unbiased_lens_structure E := pr2 E.

Definition lens_lext {B : rxgraph}
  {E : ∏ {a b : B}, a ≈ b -> rxgraph} (ℓ : unbiased_lens_structure (@E))
  : ∏ {x y : B} (e : x ≈ y) (a : E (refl x)), E e := pr1 ℓ.
Definition lens_rext {B : rxgraph}
  {E : ∏ {a b : B}, a ≈ b -> rxgraph} (ℓ : unbiased_lens_structure (@E))
  : ∏ {x y : B} (e : x ≈ y) (a : E (refl y)), E e := pr12 ℓ.
Definition lens_ext_refl {B : rxgraph}
  {E : ∏ {a b : B}, a ≈ b -> rxgraph} (ℓ : unbiased_lens_structure (@E))
  : ∏ (x : B) (a : E (refl x)), lens_lext ℓ (refl x) a ≈ lens_rext ℓ (refl x) a := pr122 ℓ.
Definition lens_rext_refl {B : rxgraph}
  {E : ∏ {a b : B}, a ≈ b -> rxgraph} (ℓ : unbiased_lens_structure (@E))
  : ∏ (x : B) (a : E (refl x)), a ≈ lens_rext ℓ (refl x) a := pr222 ℓ.

Definition unbiased_lens_disp_rxgraph {B : rxgraph}
  (E : unbiased_lens B) : disp_rxgraph B.
Proof.
  use make_disp_rxgraph.
  - intro x; exact (E _ _ (refl x)).
  - intros x y e a b.
    exact (lens_lext E e a ≈ lens_rext E e b).
  - intros x a.
    exact (lens_ext_refl E x a).
Defined.

Notation "'disp±'" := unbiased_lens_disp_rxgraph.
(* type in Emacs using agda-input with disp \pm *)

Lemma is_univalent_unbiased_lens_disp_rxgraph
  {B : rxgraph} (E : unbiased_lens B)
  (HE : ∏ (x y : B) (e : x ≈ y), is_univalent (E _ _ e))
  : is_disp_univalent (disp± E).
Proof.
  intro x.
  apply is_univalent_from_isaprop_edges_from; intro a.
  use (isofhlevelweqb 1 (Y:=edges_from (E _ _ (refl x)) (lens_lext E (refl x) a))).
  - apply weqfibtototal; intro b; cbn.
    elim (lens_rext_refl E x b) using rxgraph_edge_rect_left.
    + apply HE.
    + exact (idweq _).
  - apply is_univalent_to_isaprop_edges_from, HE.
Qed.

Lemma iscontr_unbiased_lens_structure_over_univalent
  {B : rxgraph} (E : ∏ {x y : B}, x ≈ y -> rxgraph)
  (HB : is_univalent B)
  (HE : ∏ (x y : B) (e : x ≈ y), is_univalent (E e))
  : iscontr (unbiased_lens_structure (@E)).
Proof.
  unfold unbiased_lens_structure.
  eapply (isofhlevelweqf 0
            (X:=(∏ x, ∑ (lext : ∏ (y : B) (e : x ≈ y), E x x (refl x) → E x y e)
                        (rext : ∏ (y : B) (e : x ≈ y), E y y (refl y) → E x y e),
                  (∏ (a : E x x (refl x)), lext x (refl x) a ≈ rext x (refl x) a)
                    × (∏ (a : E x x (refl x)), a ≈ rext x (refl x) a)))).
  { use weq_iso.
    - intros f.
      exact ((λ x, pr1 (f x)),, (λ x, pr12 (f x)),,
               (λ x, pr122 (f x)),, (λ x, pr222 (f x))).
    - intros [lext [rext [eq eqr]]] x.
      exact (lext x,, rext x,, eq x,, eqr x).
    - easy.
    - easy. }
  apply impred; intro x.
  eapply (isofhlevelweqb 0
            (Y:=∑ (lext rext : E _ _ (refl x) -> E _ _ (refl x)),
               (lext ≈{_ ~> _} rext) × (idfun _ ≈{_ ~> _} rext))). {
    use weqbandf; [apply (weq_sec_over_contr_total2 (is_univalent_to_iscontr_edges_from _ HB x))|].
    intro lext; cbn.
    use weqbandf; [apply (weq_sec_over_contr_total2 (is_univalent_to_iscontr_edges_from _ HB x))|].
    intro rext; cbn.
    exact (idweq _).
  }
  eapply (isofhlevelweqb 0 (Y:=edges_to (_ ~> _) (idfun (E _ _ (refl x))))).
  { apply weqfibtototal; intro lext.
    intermediate_weq (∑ (rext : edges_from (_ ~> _) (idfun (E _ _ (refl x)))),
                       lext ≈{_ ~> _} pr1 rext).
    { use weq_iso.
      - intros [r [p q]]; exact ((r,,q),,p).
      - intros [[r q] p]; exact (r,, p,, q).
      - easy.
      - easy. }
    refine (weqcomp _ (weqtotal2overunit (λ _, _))).
    apply invweq.
    use weqbandf. {
      apply wequnittocontr, is_univalent_to_iscontr_edges_from.
      apply is_univalent_product_rxgraph; intro; apply HE.
    }
    intro; exact (idweq _).
  }
  apply is_univalent_to_iscontr_edges_to.
  apply is_univalent_product_rxgraph; intro; apply HE.
Qed.

(** Unbiased lenses from biased ones *)

Definition unbiased_lens_from_covy {B : rxgraph}
  (E : covy_lens B) : unbiased_lens B.
Proof.
  use make_unbiased_lens.
  - intros x y e; exact (E y).
  - intros x y e; exact (lens_push E e).
  - intros x y e; exact (idfun (E y)).
  - intros x a; exact (lens_push_refl E x a).
  - intros x a; exact (refl a).
Defined.

Lemma unbiased_lens_from_covy_disp_compute
  {B : rxgraph} (E : covy_lens B)
  : disp± (unbiased_lens_from_covy E) = disp+ E.
Proof. reflexivity. Defined.

Definition unbiased_lens_from_contra {B : rxgraph}
  (E : contra_lens B) : unbiased_lens B.
Proof.
  use make_unbiased_lens.
  - intros x y e; exact (E x).
  - intros x y e; exact (idfun (E x)).
  - intros x y e; exact (lens_pull E e).
  - intros x a; exact (lens_pull_refl E x a).
  - intros x a; exact (lens_pull_refl E x a).
Defined.

Lemma unbiased_lens_from_contra_disp_compute
  {B : rxgraph} (E : contra_lens B)
  : disp± (unbiased_lens_from_contra E) = disp- E.
Proof. reflexivity. Defined.

(** ** Definitional lenses *)

Definition discrete_covy_lens {B : UU} (E : B -> rxgraph)
  : @covy_lens_structure (Δ B) E.
Proof.
  use make_covy_lens_structure.
  - intros x y e; exact (transportf E e).
  - intros x a; exact (refl a).
Defined.

Definition make_discrete_covy_lens {B : UU} (E : B -> rxgraph) : covy_lens (Δ B)
  := E,, discrete_covy_lens E.

Notation "'Δ+' x ',' E" :=
  (make_discrete_covy_lens (λ x, E))
    (x binder, at level 200) : rxgraph.
(* type in Emacs using agda-input with \Delta or \GD *)

Definition discrete_contra_lens {B : UU} (E : B -> rxgraph)
  : @contra_lens_structure (Δ B) E.
Proof.
  use make_contra_lens_structure.
  - intros x y e; exact (transportb E e).
  - intros x a; exact (refl a).
Defined.

Definition make_discrete_contra_lens {B : UU} (E : B -> rxgraph) : contra_lens (Δ B)
  := E,, discrete_contra_lens E.

Notation "'Δ-' x ',' E" :=
  (make_discrete_contra_lens (λ x, E))
    (x binder, at level 200) : rxgraph.
(* type in Emacs using agda-input with \Delta or \GD *)

(** Definitional replacement *)

Definition flatten_covy_lens {B : rxgraph}
  (E : covy_lens B) : rxgraph.
Proof.
  use make_rxgraph.
  - exact B.
  - intros x y.
    exact (∑ (e : x ≈ y) (e' : E x -> E y),
            ∏ (a : E x), lens_push E e a ≈ e' a).
  - intro x; cbn.
    exists (refl x), (idfun (E x)).
    exact (lens_push_refl E x).
Defined.

Lemma is_univalent_flatten_covy_lens
  {B : rxgraph} (E : covy_lens B)
  (HB : is_univalent B)
  (HE : ∏ x, is_univalent (E x))
  : is_univalent (flatten_covy_lens E).
Proof.
  apply is_univalent_from_weq.
  cbn; intros x y.
  apply (weqcomp (weq_id_to_edge HB x y)).
  apply invweq, weqpr1; intro e.
  refine (is_univalent_to_iscontr_edges_from (_ ~> E y) _ (lens_push E e)).
  apply is_univalent_product_rxgraph; intro a.
  apply HE.
Qed.

Definition flatten_covy_lens_structure
  {B : rxgraph} (E : covy_lens B)
  : @covy_lens_structure (flatten_covy_lens E) E.
Proof.
  use make_covy_lens_structure.
  - intros x y [e [e' f]].
    exact e'.
  - intros x a; exact (refl a).
Defined.

Definition flatten_contra_lens {B : rxgraph}
  (E : contra_lens B) : rxgraph.
Proof.
  use make_rxgraph.
  - exact B.
  - intros x y.
    exact (∑ (e : x ≈ y) (e' : E y -> E x),
            ∏ (a : E y), e' a ≈ lens_pull E e a).
  - intro x; cbn.
    exists (refl x), (idfun (E x)).
    exact (lens_pull_refl E x).
Defined.

Lemma is_univalent_flatten_contra_lens
  {B : rxgraph} (E : contra_lens B)
  (HB : is_univalent B)
  (HE : ∏ x, is_univalent (E x))
  : is_univalent (flatten_contra_lens E).
Proof.
  apply is_univalent_from_weq.
  cbn; intros x y.
  apply (weqcomp (weq_id_to_edge HB x y)).
  apply invweq, weqpr1; intro e.
  refine (is_univalent_to_iscontr_edges_to (_ ~> E x) _ (lens_pull E e)).
  apply is_univalent_product_rxgraph; intro a.
  apply HE.
Qed.

Definition flatten_contra_lens_structure
  {B : rxgraph} (E : contra_lens B)
  : @contra_lens_structure (flatten_contra_lens E) E.
Proof.
  use make_contra_lens_structure.
  - intros x y [e [e' f]].
    exact e'.
  - intros x a; exact (refl a).
Defined.
