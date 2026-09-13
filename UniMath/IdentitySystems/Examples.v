(********************************************************************************

 Constructions of reflexive graphs

 This file contains a zoo of reflexive graph constructions,
 corresponding to various type constructors.

 Contains:
 - Reflexive graphs:
   discrete (Δ), codiscrete (∇),
   product (∏), binary product (×),
   binary coproduct (⨿), universe ([UU_rxgraph]),
   opposite (^op), total ([total_rxgraph]),
   component (⟦⟧), sub- ({ ∣ }).
 - Displayed reflexive graphs:
   sigma, discrete, trivial, total opposite.
 - Notations for the above.

 Author: B. Szilvasy
 February—September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.

Local Open Scope rxgraph.

(** ** Reflexive graphs *)

(** The discrete reflexive graph [Δ A] is the reflexive graph whose vertices are
    [A] and whose edges are identifications.  It is always univalent. *)

Definition discrete_rxgraph (A : UU) : univalent_rxgraph.
Proof.
  use make_univalent_rxgraph.
  - use make_rxgraph.
    + exact A.
    + exact (@paths A).
    + exact idpath.
  - apply is_univalent_from_iscontr_edges_from; intro.
    exact (iscontr_paths_from _).
Defined.

(** The codiscrete reflexive graph [∇ A] has vertices [A]
    and edges [unit].  It is univalent if [A] is a proposition. *)

Definition codiscrete_rxgraph (A : UU) : rxgraph.
Proof.
  use make_rxgraph.
  - exact A.
  - exact (λ _ _, unit).
  - easy.
Defined.

Definition is_univalent_codiscrete_rxgraph (A : UU)
  (H : isaprop A)
  : is_univalent (codiscrete_rxgraph A).
Proof.
  apply is_univalent_from_weq.
  intros a b; apply weqcontrtounit, H.
Qed.

Definition prop_rxgraph (A : UU) (H : isaprop A) : univalent_rxgraph
  := make_univalent_rxgraph _ (is_univalent_codiscrete_rxgraph A H).

Definition hProp_rxgraph (A : hProp) : univalent_rxgraph
  := prop_rxgraph A (propproperty A).

(** A family of reflexive graphs [x : B ⊢ E[x]] gives rise to a univalent
    reflexive graph whose vertices are [∏ x, E[x]].  It is univalent
    if all [E] are (assuming function extensionality). *)

Definition product_rxgraph {B : UU} (E : B -> rxgraph) : rxgraph.
Proof.
  use make_rxgraph.
  - exact (∏ x, E x).
  - intros f g.
    exact (∏ x, f x ≈ g x).
  - intros f x.
    exact (refl (f x)).
Defined.

Definition is_univalent_product_rxgraph {B : UU} (E : B -> rxgraph)
  (H : ∏ x, is_univalent (E x))
  : is_univalent (product_rxgraph E).
Proof.
  use is_univalent_from_weq.
  intros f g.
  apply (weqcomp (weqtoforallpaths _ _ _)).
  use weqonsecfibers; intro a.
  apply (weq_id_to_edge (H a)).
Qed.

Definition product_univalent_rxgraph {B : UU} (E : B -> univalent_rxgraph) : univalent_rxgraph
  := make_univalent_rxgraph _ (is_univalent_product_rxgraph E (λ x, E x)).

(** The binary product [A × B] of reflexive graphs [A] and [B] has the obvious
    vertices and edges the binary products of [A]- and [B]-edges.  It is univalent
    if both [A] and [B] are. *)

Definition dirprod_rxgraph (A B : rxgraph) : rxgraph.
Proof.
  use make_rxgraph.
  - exact (A × B).
  - intros a b.
    exact (pr1 a ≈ pr1 b × pr2 a ≈ pr2 b).
  - intro a.
    exact (refl (pr1 a),, refl (pr2 a)).
Defined.

Lemma is_univalent_dirprod_rxgraph (A B : rxgraph)
  (HA : is_univalent A)
  (HB : is_univalent B)
  : is_univalent (dirprod_rxgraph A B).
Proof.
  apply is_univalent_from_weq.
  intros aa bb.
  apply (weqcomp pathsdirprodweq).
  apply weqdirprodf.
  - apply (weq_id_to_edge HA).
  - apply (weq_id_to_edge HB).
Qed.

Definition dirprod_univalent_rxgraph (A B : univalent_rxgraph) : univalent_rxgraph
  := make_univalent_rxgraph _ (is_univalent_dirprod_rxgraph _ _ A B).

(** The (binary) coproduct reflexive graph [A ⨿ B] has the obvious vertices.
    Its edges [inl a₁ ≈ inl a₂] are [a₁ ≈ a₂], and edges [inr b₁ ≈ inr b₂] are
    [b₁ ≈ b₂], while the other two edges are [empty].  It is univalent if [A]
    and [B] are. *)

Definition coprod_edges
  {A B : rxgraph}
  (x y : A ⨿ B)
  : UU.
Proof.
  induction x as [a₁ | b₁];
    induction y as [a₂ | b₂].
  - exact (a₁ ≈ a₂).
  - exact empty.
  - exact empty.
  - exact (b₁ ≈ b₂).
Defined.

Definition coprod_refl
  {A B : rxgraph}
  (x : A ⨿ B)
  : coprod_edges x x.
Proof.
  induction x as [a | b]; apply refl.
Defined.

Definition coprod_rxgraph (A B : rxgraph) : rxgraph.
Proof.
  use make_rxgraph.
  - exact (A ⨿ B).
  - exact (@coprod_edges A B).
  - exact (@coprod_refl A B).
Defined.

Definition is_univalent_coprod_rxgraph
  (A B : rxgraph)
  (HA : is_univalent A)
  (HB : is_univalent B)
  : is_univalent (coprod_rxgraph A B).
Proof.
  use is_univalent_from_weq.
  intros x y.
  apply (weqcomp (equality_by_case_equiv x y)).
  induction x as [a₁ | b₁]; induction y as [a₂ | b₂]; cbn.
  - apply (weq_id_to_edge HA).
  - exact (idweq empty).
  - exact (idweq empty).
  - apply (weq_id_to_edge HB).
Qed.

Definition coprod_univalent_rxgraph
  (A B : univalent_rxgraph)
  : univalent_rxgraph
  := make_univalent_rxgraph _
       (is_univalent_coprod_rxgraph A B A B).

(** [UU_rxgraph] is the (large) reflexive graph of (small) types.
    It is univalent precisely if the universe is.  We indicate
    the larger size with an imaginary universe parameter [ℓ]. *)

Definition UU_rxgraph (* ℓ *) : rxgraph (* ℓ+1 *).
Proof.
  use make_rxgraph.
  - exact (UU (* ℓ *)).
  - exact weq.
  - exact idweq.
Defined.

Goal univalenceStatement = is_univalent UU_rxgraph.
Proof.
  reflexivity.
Qed.

Definition UU_univalent_rxgraph (* ℓ *) : univalent_rxgraph (* ℓ+1 *)
  := make_univalent_rxgraph UU_rxgraph univalenceAxiom.

(** A family of types [x : B ⊢ E[x]] gives a reflexive graph [B/E] called the image of the family. *)

Definition family_image_rxgraph (B : UU) (E : B -> UU) : rxgraph.
Proof.
  use make_rxgraph.
  - exact B.
  - intros a b; exact (E a ≃ E b).
  - intro a; exact (idweq (E a)).
Defined.

(** The opposite [G^op] of a reflexive graph [G] has the same vertices, but
    flipped edges.  It is univalent if and only if G is. *)

Definition opp_rxgraph (A : rxgraph) : rxgraph.
Proof.
  use make_rxgraph.
  - exact A.
  - intros a b.
    exact (b ≈ a).
  - intro a.
    exact (refl a).
Defined.

Lemma opp_opp_rxgraph_compute (A : rxgraph)
  : opp_rxgraph (opp_rxgraph A) = A.
Proof. reflexivity. Defined.

Lemma is_univalent_opp_rxgraph (A : rxgraph)
  (HA : is_univalent A)
  : is_univalent (opp_rxgraph A).
Proof.
  apply (is_univalent_from_isaprop_edges_from (opp_rxgraph A)).
  exact (is_univalent_to_isaprop_edges_to A HA).
Defined.

Definition opp_univalent_rxgraph (A : univalent_rxgraph) : univalent_rxgraph
  := make_univalent_rxgraph _ (is_univalent_opp_rxgraph _ A).

(** A displayed reflexive graph [x : B |- E[x]] gives a reflexive graph
    whose vertices are sigma types.  It is univalent if [B] and [E] are. *)

Definition total_rxgraph
  {B : rxgraph} (E : disp_rxgraph B) : rxgraph.
Proof.
  use make_rxgraph.
  - exact (∑ x, E x).
  - intros [x a] [y b].
    exact (∑ (e : x ≈ y), a ≈[e] b).
  - intros [x a].
    exists (refl x).
    exact (disp_refl x a).
Defined.

Definition is_univalent_total_rxgraph
  {B : rxgraph} (E : disp_rxgraph B)
  (HB : is_univalent B)
  (HE : is_disp_univalent E)
  : is_univalent (total_rxgraph E).
Proof.
  apply is_univalent_from_weq.
  intros xa yb.
  apply (weqcomp (total2_paths_equiv' _ _ _)).
  use weqbandf; cbn.
  - apply (weq_id_to_edge HB).
  - intro e.
    apply (weqcomp (transportf_weq_pathover _ _ _)).
    apply (weq_PathOver_to_disp_edge HE).
Qed.

Definition total_univalent_rxgraph
  {B : univalent_rxgraph} (E : univalent_disp_rxgraph B)
  : univalent_rxgraph
  := make_univalent_rxgraph _ (is_univalent_total_rxgraph E B E).

(** A displayed reflexive graph's components are (by definition) univalent if
    the displayed reflexive graph is. *)

Definition is_univalent_disp_rxgraph_at
  {B : rxgraph} (E : disp_rxgraph B)
  (HA : is_disp_univalent E)
  : ∏ x, is_univalent (disp_rxgraph_at E x)
  := HA.

Definition univalent_disp_rxgraph_at
  {B : rxgraph} (E : univalent_disp_rxgraph B)
  (x : B)
  : univalent_rxgraph
  := make_univalent_rxgraph _
       (is_univalent_disp_rxgraph_at E E x).

(** Given a family of types [x : A ⊢ P[x]] over a reflexive graph A,
    the sub-reflexive graph of [A] satisfying [P] is the
    reflexive graph whose elements are those of [A] satisfying [P].
    It is univalent if [A] is univalent and [P] is a predicate. *)

Definition sub_rxgraph (A : rxgraph) (P : A -> UU) : rxgraph.
Proof.
  use make_rxgraph.
  - exact (∑ a, P a).
  - intros a b.
    exact (pr1 a ≈ pr1 b).
  - intros a.
    apply refl.
Defined.

Definition is_univalent_sub_rxgraph
  (A : rxgraph) (P : A -> UU)
  (HA : is_univalent A)
  (HP : isPredicate P)
  : is_univalent (sub_rxgraph A P).
Proof.
  apply is_univalent_from_weq.
  intros a b.
  refine (weqcomp (Injectivity pr1 _ a b) _).
  { apply isweqonpathsincl, isinclpr1, HP. }
  apply (weq_id_to_edge HA).
Defined.

Definition sub_univalent_rxgraph
  (A : univalent_rxgraph) (P : A -> hProp)
  : univalent_rxgraph
  := make_univalent_rxgraph _
       (is_univalent_sub_rxgraph A P A
          (λ x, propproperty (P x))).

Definition sub_univalent_rxgraph_pred
  (A : univalent_rxgraph) (P : A -> UU)
  (HP : isPredicate P)
  : univalent_rxgraph
  := make_univalent_rxgraph _
       (is_univalent_sub_rxgraph A P A HP).

(** A displayed reflexive graph [E₁] over [B], along with a
    displayed reflexive graph [E₂] over the total reflexive graph of [E₁],
    gives rise to a displayed reflexive graph over [B] whose
    vertices are the sums of [E₁].  It is univalent if [E₁] and [E₂] are. *)

Definition sigma_disp_rxgraph
  {B : rxgraph}
  (E₁ : disp_rxgraph B)
  (E₂ : disp_rxgraph (total_rxgraph E₁))
  : disp_rxgraph B.
Proof.
  use make_disp_rxgraph.
  - intro x; exact (∑ (e₁ : E₁ x), E₂ (x,, e₁)).
  - intros x y p [e₁ e₂] [e₁' e₂'].
    refine (∑ (p₁ : e₁ ≈[p] e₁'), e₂ ≈[_] e₂').
    exact (p,,p₁).
  - intros x [e₁ e₂].
    exists (disp_refl x e₁).
    exact (disp_refl _ e₂).
Defined.

(** Components of [sigma_disp_rxgraph] wind up being the total reflexive graph of
    the following displayed reflexive graph over the components of [E₁]. *)

Definition sigma_disp_rxgraph_at
  {B : rxgraph}
  (E₁ : disp_rxgraph B)
  (E₂ : disp_rxgraph (total_rxgraph E₁))
  (x : B)
  : disp_rxgraph (disp_rxgraph_at E₁ x).
Proof.
  use make_disp_rxgraph.
  - intro e₁; exact (E₂ (x,,e₁)).
  - intros e₁ e₁' p₁ e₂ e₂'.
    refine (e₂ ≈[_] e₂').
    exact (refl _,,p₁).
  - intros e₁ e₂.
    cbn in e₂.
    exact (disp_refl _ e₂).
Defined.

Definition is_univalent_sigma_disp_rxgraph
  {B : rxgraph}
  (E₁ : disp_rxgraph B)
  (E₂ : disp_rxgraph (total_rxgraph E₁))
  (H₁ : is_disp_univalent E₁)
  (H₂ : is_disp_univalent E₂)
  : is_disp_univalent (sigma_disp_rxgraph E₁ E₂).
Proof.
  intro x.
  change (is_univalent (total_rxgraph (sigma_disp_rxgraph_at E₁ E₂ x))).
  apply is_univalent_total_rxgraph.
  - exact (H₁ x).
  - intro e₁.
    exact (H₂ _).
Qed.

Definition sigma_univalent_disp_rxgraph
  {B : rxgraph}
  (E₁ : univalent_disp_rxgraph B)
  (E₂ : univalent_disp_rxgraph (total_rxgraph E₁))
  : univalent_disp_rxgraph B
  := _,, is_univalent_sigma_disp_rxgraph E₁ E₂ E₁ E₂.

(** A family of types [x : B |- E[x]] gives rise to a discrete displayed
    reflexive graph whose vertices are the [PathPair]s.  It is always
    univalent. *)

Definition discrete_disp_rxgraph {B : UU} (E : B -> UU)
  : univalent_disp_rxgraph (discrete_rxgraph B).
Proof.
  use make_univalent_disp_rxgraph.
  - use make_disp_rxgraph.
    + exact E.
    + intros x y e a b.
      exact (PathOver e a b).
    + easy.
  - intros x a b.
    apply (weqhomot _ (idweq (a = b))).
    intro p; now induction p.
Defined.

(** A reflexive graph [E] lifts trivially to a displayed reflexive graph over
    another. *)

Definition trivial_disp_rxgraph (B E : rxgraph)
  : disp_rxgraph B.
Proof.
  use make_disp_rxgraph.
  - intro; exact E.
  - intros x y e; exact (edge E).
  - intro; exact refl.
Defined.

Lemma trivial_disp_rxgraph_at_compute
  (B E : rxgraph) (x : B)
  : disp_rxgraph_at (trivial_disp_rxgraph B E) x = E.
Proof. reflexivity. Defined.

Definition trivial_univalent_disp_rxgraph
  (B : rxgraph) (E : univalent_rxgraph)
  : univalent_disp_rxgraph B
  := make_univalent_disp_rxgraph
       (trivial_disp_rxgraph B E)
       (λ x, E).

(** The total opposite of a displayed reflexive graph [x : B ⊢ E[x]]
    is the displayed reflexive graph over [B^op] with the same
    vertices as [E] but flipped edges.  It is univalent if [E] is. *)

Definition total_opp_disp_rxgraph
  {B : rxgraph} (E : disp_rxgraph B)
  : disp_rxgraph (opp_rxgraph B).
Proof.
  use make_disp_rxgraph.
  - exact E.
  - intros x y e a b; cbn in e.
    exact (b ≈[e] a).
  - intros x a; cbn in x.
    exact (disp_refl x a).
Defined.

Definition is_univalent_total_opp_disp_rxgraph
  {B : rxgraph} (E : disp_rxgraph B)
  (HE : is_disp_univalent E)
  : is_disp_univalent (total_opp_disp_rxgraph E).
Proof.
  intro x.
  apply is_univalent_from_isaprop_edges_from.
  exact (is_univalent_to_isaprop_edges_to _ (HE x)).
Qed.

Lemma total_opp_opp_disp_rxgraph_compute
  {B : rxgraph} (E : disp_rxgraph B)
  : total_opp_disp_rxgraph (total_opp_disp_rxgraph E) = E.
Proof. reflexivity. Defined.

Definition total_opp_univalent_disp_rxgraph
  {B : rxgraph} (E : univalent_disp_rxgraph B)
  : univalent_disp_rxgraph (opp_rxgraph B)
  := make_univalent_disp_rxgraph _
       (is_univalent_total_opp_disp_rxgraph E E).

(** ** Notations for building reflexive graphs. *)

Notation "'Δ' A" := (discrete_rxgraph A) (at level 200) : rxgraph_spec.
(* type in Emacs using agda-input with \Delta or \GD *)

Notation "'∇' A" := (codiscrete_rxgraph A) (at level 200) : rxgraph_spec.
Notation "'∇![' H  ']' A" := (prop_rxgraph A H) (at level 200) : rxgraph_spec.
Notation "'∇!' A" := (hProp_rxgraph A) (at level 200) : rxgraph_spec.
(* type in Emacs using agda-input with \nabla *)

Notation "'∏' x .. y , G" :=
  (product_rxgraph (λ x, .. (product_rxgraph (λ y, G%rxgraph_spec)) ..)) : rxgraph_spec.
Notation "'∏!' x .. y , G" :=
  (product_univalent_rxgraph (λ x, .. (product_univalent_rxgraph (λ y, G%rxgraph_spec)) ..))
    (at level 200, x binder, y binder, right associativity) : rxgraph_spec.
(* type in Emacs using agda-input with \prod *)

Notation "A × B" := (dirprod_rxgraph A%rxgraph_spec B%rxgraph_spec) : rxgraph_spec.
Notation "A '×!' B" := (dirprod_univalent_rxgraph A%rxgraph_spec B%rxgraph_spec)
                         (at level 75, right associativity) : rxgraph_spec.
(* type in Emacs using agda-input with \times *)

Notation "A ⨿ B" := (coprod_rxgraph A%rxgraph_spec B%rxgraph_spec) : rxgraph_spec.
Notation "A '⨿!' B" := (coprod_univalent_rxgraph A%rxgraph_spec B%rxgraph_spec) (at level 75, right associativity) : rxgraph_spec.
(* type in Emacs with C-X 8 RET AMALGAMATION OR COPRODUCT
   or using agda-input with \union (on the second page). *)

Notation "B '/' E" := (family_image_rxgraph B%rxgraph_spec E%rxgraph_spec) : rxgraph_spec.

Notation "A '^op'" := (opp_rxgraph A%rxgraph_spec) (at level 1, format "A ^op") : rxgraph_spec.
Notation "A '^op!'" := (opp_univalent_rxgraph A%rxgraph_spec) (at level 1, format "A ^op!") : rxgraph_spec.

Notation "E ⟦ x ⟧" := (disp_rxgraph_at E%rxgraph_spec x) (at level 49) : rxgraph_spec.
Notation "E ⟦ x '⟧!'" := (univalent_disp_rxgraph_at E%rxgraph_spec x) (at level 49) : rxgraph_spec.
(* type in Emacs using agda-input with \[[ \]] *)

Notation "'{'  x '∣' P  '}'" := (sub_rxgraph _ (λ (x : _%rxgraph_spec), P)) (x binder) : rxgraph_spec.
Notation "'{'  x '∣!' P  '}'" := (sub_univalent_rxgraph _ (λ x, P)) (x binder) : rxgraph_spec.
Notation "'{'  x '∣![' H  ']' P  '}'" :=
  (sub_univalent_rxgraph_pred _ (λ (x : _%rxgraph_spec), P) (λ x, H)) (x binder) : rxgraph_spec.
(* type in Emacs using agda-input with \mid *)
