(********************************************************************************

 The Reflexive Graph of Reflexive Graphs

 We classify the identifications of (small) reflexive graphs and displayed
 reflexive graphs using (large) reflexive graphs.  The work here is based on Jon
 Sterling, 2026, "Reflexive graph lenses in Univalent Foundations"
 (doi:10.1017/S0960129526100565, arXiv:2404.07854).

 Users of this library should note the size issues: vertices of
 [rxgraph_rxgraph] should be considered *small* reflexive graphs, while
 [rxgraph_rxgraph] itself is a *large* reflexive graph.  In particular,
 [rxgraph_rxgraph] should not be considered as an element of itself, but as an
 element of a larger [rxgraph_rxgraph].  We annotate definitions in this file
 which use multiple universes with an imaginary level parameter [ℓ] (\ell) to
 clarify.

 Contents:
 1. Reflexive graph of graphs
 2. Reflexive graph of [rxgraph]s
 3. Reflexive graph of displayed graphs
 4. Reflexive graph of [disp_rxgraph]s
 5. Displayed reflexive graph of [disp_rxgraph]s

 Author: B. Szilvasy
 September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.
Require Import UniMath.IdentitySystems.Lenses.

Local Open Scope rxgraph.
Local Bind Scope rxgraph_spec with rxgraph.
Local Bind Scope rxgraph_spec with univalent_rxgraph.

(** ** Reflexive graph of graphs *)

Definition graph_on_rxgraph (* ℓ *)
  : contra_lens (* ℓ+1 *) (UU_rxgraph (* ℓ *)).
Proof.
  use make_contra_lens.
  - intros A; exact (∏ (_ _ : A), UU_rxgraph (* ℓ *))%rxgraph_spec.
  - intros x y w e; cbn in w, e.
    exact (λ x' y', e (w x') (w y')).
  - intros A edge; exact (refl edge).
Defined.

Lemma is_univalent_graph_on_rxgraph (* ℓ *) (A : UU (* ℓ *))
  : is_univalent (* ℓ+1 *) (graph_on_rxgraph (* ℓ *) A).
Proof. exact (∏! _ _, UU_univalent_rxgraph)%rxgraph_spec. Qed.

Definition graph_rxgraph (* ℓ *) : rxgraph (* ℓ+1 *)
  := total_rxgraph (* ℓ+1 *)
       (contra_lens_disp_rxgraph (* ℓ+1 *) (graph_on_rxgraph (* ℓ *))).

Lemma is_univalent_graph_rxgraph (* ℓ *)
  : is_univalent (* ℓ+1 *) (graph_rxgraph (* ℓ *)).
Proof.
  apply is_univalent_total_rxgraph.
  - exact UU_univalent_rxgraph.
  - apply is_univalent_contra_lens_disp_rxgraph; intro A.
    apply is_univalent_graph_on_rxgraph.
Qed.

Definition graph_univalent_rxgraph (* ℓ *) : univalent_rxgraph (* ℓ+1 *)
  := make_univalent_rxgraph (* ℓ+1 *) _ is_univalent_graph_rxgraph.

Definition graph_iso (* ℓ *) (C D : graph_rxgraph (* ℓ *)) : UU (* ℓ *) := C ≈ D.
Identity Coercion Id_graph_iso : graph_iso >-> edge.

Coercion graph_iso_on_vertex {C D : graph_rxgraph}
  (w : graph_iso C D) : pr1 C ≃ pr1 D := pr1 w.
Definition graph_iso_on_edge {C D : graph_rxgraph}
  (w : graph_iso C D)
  : ∏ {a b : pr1 C}, pr2 C a b ≃ pr2 D (w a) (w b)
  := pr2 w.

Definition make_graph_iso (C D : graph_rxgraph)
  (v : pr1 C ≃ pr1 D)
  (e : ∏ (a b : pr1 C), pr2 C a b ≃ pr2 D (v a) (v b))
  : graph_iso C D
  := v,, e.

(** ** Reflexive graph of [rxgraph]s *)

Definition has_refl_rxgraph (* ℓ *)
  : unbiased_lens (* ℓ+1 *) (graph_rxgraph (* ℓ *)).
Proof.
  use make_unbiased_lens.
  - intros C D f.
    change (graph_iso C D) in f.
    exact (∏ (a : pr1 C), Δ pr2 D (f a) (f a))%rxgraph_spec.
  - intros C D f refl a.
    change (graph_iso C D) in f.
    cbn in refl.
    exact (graph_iso_on_edge f (refl a)).
  - intros C D f refl a.
    change (graph_iso C D) in f.
    cbn in refl.
    exact (refl (f a)).
  - intros C refl'; exact (refl refl').
  - intros C refl'; exact (refl refl').
Defined.

Lemma is_univalent_has_refl_rxgraph (* ℓ *)
  {C D : graph_rxgraph (* ℓ *)} (w : graph_iso (* ℓ *) C D)
  : is_univalent (* ℓ+1 *) (has_refl_rxgraph (* ℓ *) C D w).
Proof. exact (∏! _, Δ _)%rxgraph_spec. Qed.

(* We defined [rxgraph] associated to the right, which means the [total_rxgraph]
   of [has_refl_rxgraph] is the wrong thing.  We can use [sigma_disp_rxgraph] to
   associate to the right as needed. *)
Definition rxgraph_rxgraph (* ℓ *) : rxgraph (* ℓ+1 *)
  := total_rxgraph (* ℓ+1 *)
       (sigma_disp_rxgraph (* ℓ+1 *) _
          (unbiased_lens_disp_rxgraph (* ℓ+1 *)
             (has_refl_rxgraph (* ℓ *)))).

Example rxgraph_vertex_rxgraph_rxgraph_compute (* ℓ *)
  : rxgraph_vertex (* ℓ+1 *) (rxgraph_rxgraph (* ℓ *))
    = rxgraph (* ℓ *).
Proof. reflexivity. Defined.

Lemma is_univalent_rxgraph_rxgraph (* ℓ *)
  : is_univalent (* ℓ+1 *) (rxgraph_rxgraph (* ℓ *)).
Proof.
  use is_univalent_total_rxgraph.
  - exact UU_univalent_rxgraph.
  - apply is_univalent_sigma_disp_rxgraph.
    + apply is_univalent_contra_lens_disp_rxgraph; intro A.
      apply is_univalent_graph_on_rxgraph.
    + apply is_univalent_unbiased_lens_disp_rxgraph.
      intros C D w.
      apply is_univalent_has_refl_rxgraph.
Qed.

Definition rxgraph_univalent_rxgraph (* ℓ *) : univalent_rxgraph (* ℓ+1 *)
  := make_univalent_rxgraph _ is_univalent_rxgraph_rxgraph.

Definition rxgraph_iso (C D : rxgraph) : UU := C ≈{rxgraph_rxgraph} D.
Identity Coercion Id_rxgraph_iso : graph_iso >-> edge.

Coercion rxgraph_iso_on_vertex {C D : rxgraph}
  (w : rxgraph_iso C D) : C ≃ D := pr1 w.
Definition rxgraph_iso_on_edge {C D : rxgraph}
  (w : rxgraph_iso C D)
  : ∏ {a b : C}, a ≈ b ≃ w a ≈ w b
  := pr12 w.
Definition rxgraph_iso_on_refl {C D : rxgraph}
  (w : rxgraph_iso C D)
  : ∏ (a : C), rxgraph_iso_on_edge w (refl a) = refl (w a)
  := pr22 w.

Definition make_rxgraph_iso (C D : rxgraph)
  (verts : C ≃ D)
  (edges : ∏ {a b : C}, a ≈ b ≃ verts a ≈ verts b)
  (refls : ∏ (a : C), edges (refl a) = refl (verts a))
  : rxgraph_iso C D
  := verts,, @edges,, refls.

Definition is_univalent_rxgraph_iso_f
  (C D : rxgraph) (F : rxgraph_iso C D)
  (H : is_univalent C) : is_univalent D.
Proof.
  apply is_univalent_from_isaprop_edges_from; intro a.
  apply (isofhlevelweqb 1 (Y:=(edges_from C (invmap F a)))).
  - apply (weqbandf (invweq F)); intro b.
    intermediate_weq (F (invmap F a) ≈ F (invmap F b)).
    { rewrite !(homotweqinvweq F).
      exact (idweq (a ≈ b)). }
    apply invweq, (rxgraph_iso_on_edge F).
  - apply is_univalent_to_isaprop_edges_from, H.
Qed.

Definition is_univalent_rxgraph_iso_b
  (C D : rxgraph) (F : rxgraph_iso C D)
  (H : is_univalent D) : is_univalent C.
Proof.
  apply is_univalent_from_isaprop_edges_from; intro a.
  apply (isofhlevelweqb 1 (Y:=(edges_from D (F a)))).
  - apply (weqbandf F); intro b.
    exact (rxgraph_iso_on_edge F).
  - apply is_univalent_to_isaprop_edges_from, H.
Qed.

(** ** Reflexive graph of displayed graphs *)

Definition disp_graph_on_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : contra_lens (* ℓ+1 *) (∏ (_ : B), UU_rxgraph (* ℓ *)).
Proof.
  use make_contra_lens.
  - intro E.
    exact (∏ (x y : B) (e : x ≈ y) (_ : E x) (_ : E y),
            UU_rxgraph (* ℓ *))%rxgraph_spec.
  - cbn; intros E₁ E₂ w edge x y e a b.
    exact (edge x y e (w x a) (w y b)).
  - intros E disp_edge; exact (refl disp_edge).
Defined.

Lemma is_univalent_disp_graph_on_rxgraph (* ℓ *)
  (B : rxgraph (* ℓ *)) (E : B -> UU (* ℓ *))
  : is_univalent (* ℓ+1 *) (disp_graph_on_rxgraph (* ℓ *) B E).
Proof.
  do 5 (apply is_univalent_product_rxgraph; intro).
  exact UU_univalent_rxgraph.
Qed.

Definition disp_graph_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : rxgraph (* ℓ+1 *)
  := total_rxgraph (* ℓ+1 *)
       (contra_lens_disp_rxgraph (* ℓ+1 *)
          (disp_graph_on_rxgraph (* ℓ *) B)).

Lemma is_univalent_disp_graph_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : is_univalent (* ℓ+1 *) (disp_graph_rxgraph (* ℓ *) B).
Proof.
  apply is_univalent_total_rxgraph.
  - exact (∏! _, UU_univalent_rxgraph)%rxgraph_spec.
  - apply is_univalent_contra_lens_disp_rxgraph; intro.
    apply is_univalent_disp_graph_on_rxgraph.
Qed.

(** ** Reflexive graph of [disp_rxgraph]s *)

Definition has_disp_refl_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : unbiased_lens (* ℓ+1 *) (disp_graph_rxgraph (* ℓ *) B).
Proof.
  use make_unbiased_lens.
  - intros C D f.
    cbn in f.
    exact (∏ (x : B) (a : pr1 C x),
            Δ pr2 D x x (refl x) (pr1 f x a) (pr1 f x a))%rxgraph_spec.
  - intros C D f disp_refl x a.
    cbn in f, disp_refl.
    exact (pr2 f _ _ (refl x) _ _ (disp_refl x a)).
  - intros C D f disp_refl x a.
    cbn in f, disp_refl.
    exact (disp_refl x (pr1 f x a)).
  - intros C disp_refl; exact (refl disp_refl).
  - intros C disp_refl; exact (refl disp_refl).
Defined.

Lemma is_univalent_has_disp_refl_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  {E₁ E₂ : disp_graph_rxgraph (* ℓ *) B} (f : E₁ ≈ E₂)
  : is_univalent (* ℓ+1 *) (has_disp_refl_rxgraph (* ℓ *) B _ _ f).
Proof.
  exact (∏! _ _, Δ _)%rxgraph_spec.
Qed.

Definition disp_rxgraph_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : rxgraph (* ℓ+1 *)
  := total_rxgraph (* ℓ+1 *)
       (sigma_disp_rxgraph (* ℓ+1 *) _
          (unbiased_lens_disp_rxgraph (* ℓ+1 *)
             (has_disp_refl_rxgraph (* ℓ *) B))).

Example rxgraph_vertex_disp_rxgraph_rxgraph_compute (* ℓ *)
  (B : rxgraph (* ℓ *))
  : rxgraph_vertex (* ℓ+1 *) (disp_rxgraph_rxgraph (* ℓ *) B)
    = disp_rxgraph (* ℓ *) B.
Proof. reflexivity. Qed.

Lemma is_univalent_disp_rxgraph_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : is_univalent (* ℓ+1 *) (disp_rxgraph_rxgraph (* ℓ *) B).
Proof.
  apply is_univalent_total_rxgraph.
  - exact (∏! _, UU_univalent_rxgraph)%rxgraph_spec.
  - apply is_univalent_sigma_disp_rxgraph.
    + apply is_univalent_contra_lens_disp_rxgraph; intro.
      apply is_univalent_disp_graph_on_rxgraph.
    + apply is_univalent_unbiased_lens_disp_rxgraph; intros x y e.
      apply is_univalent_has_disp_refl_rxgraph.
Qed.

Definition disp_rxgraph_univalent_rxgraph (* ℓ *) (B : rxgraph (* ℓ *))
  : univalent_rxgraph (* ℓ+1 *)
  := make_univalent_rxgraph (* ℓ+1 *) _
       (is_univalent_disp_rxgraph_rxgraph (* ℓ *) B).

Definition disp_rxgraph_iso {B : rxgraph} (E₁ E₂ : disp_rxgraph B) : UU
  := E₁ ≈{disp_rxgraph_rxgraph B} E₂.

Definition make_disp_rxgraph_iso
  {B : rxgraph} (E₁ E₂ : disp_rxgraph B)
  (verts : ∏ {x}, E₁ x ≃ E₂ x)
  (edges : ∏ {x y : B} (e : x ≈ y) {a : E₁ x} {b : E₁ y},
      a ≈[e] b ≃ verts a ≈[e] verts b)
  (refls : ∏ (x : B) (a : E₁ x),
      edges (refl x) (disp_refl x a) = disp_refl x (verts a))
  : disp_rxgraph_iso E₁ E₂
  := @verts,, @edges,, refls.

(** ** Displayed reflexive graph of [disp_rxgraph]s *)

Definition transportb_disp_rxgraph
  {B₁ B₂ : rxgraph} (i : rxgraph_iso B₁ B₂)
  (E : disp_rxgraph B₂)
  : disp_rxgraph B₁.
Proof.
  use make_disp_rxgraph.
  - intros x'.
    exact (E (i x')).
  - cbn; intros x y e a b.
    exact (a ≈[rxgraph_iso_on_edge i e] b).
  - cbn; intros x a.
    refine (transportb (λ e, a ≈[e] a) _ (disp_refl (i x) a)).
    exact (rxgraph_iso_on_refl i x).
Defined.

Definition disp_rxgraph_lens_structure (* ℓ *)
  : contra_lens_structure (* ℓ+1 *)
      (B:=rxgraph_rxgraph (* ℓ *))
      (disp_rxgraph_rxgraph (* ℓ *)).
Proof.
  use make_contra_lens_structure.
  - intros C D i E.
    exact (transportb_disp_rxgraph i E).
  - intros B E; exact (refl E).
Defined.

Definition disp_rxgraph_disp_rxgraph (* ℓ *)
  : disp_rxgraph (* ℓ+1 *) (rxgraph_rxgraph (* ℓ *))
  := contra_lens_disp_rxgraph (* ℓ+1 *)
       (disp_rxgraph_rxgraph (* ℓ *),, disp_rxgraph_lens_structure (* ℓ *)
         : contra_lens (* ℓ+1 *) (rxgraph_rxgraph (* ℓ *))).

Lemma is_univalent_disp_rxgraph_disp_rxgraph
  : is_disp_univalent disp_rxgraph_disp_rxgraph.
Proof.
  apply is_univalent_contra_lens_disp_rxgraph; intro.
  apply is_univalent_disp_rxgraph_rxgraph.
Qed.

Definition disp_rxgraph_univalent_disp_rxgraph (* ℓ *)
  : univalent_disp_rxgraph (* ℓ+1 *) (rxgraph_rxgraph (* ℓ *))
  := make_univalent_disp_rxgraph _ is_univalent_disp_rxgraph_disp_rxgraph.
