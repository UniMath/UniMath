(* ******************************************************************************* *)
(** * Bicategory of graphs
    Benedikt Ahrens, Marco Maggesi
    May 2018
    Revised June 2019
 ********************************************************************************* *)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Propositions.

Require UniMath.CategoryTheory.Core.Categories.  (* isaprop_has_homsets *)
Require UniMath.CategoryTheory.Core.Univalence.  (* double_transport *)
Require UniMath.CategoryTheory.Core.Functors.    (* functor_data_eq *)

(** ** Pregraphs. *)

Definition pregraph : UU
  := ∑ N : UU, N → N → UU.

Definition make_pregraph
  : ∏ N : UU, (N → N → UU) → pregraph
  := tpair _.

Definition vertex : pregraph → UU := pr1.

Definition edge
  : ∏ G : pregraph, vertex G → vertex G → UU
  := pr2.

Definition has_vertexset (G : pregraph) : UU
  := isaset (vertex G).

Definition isaprop_has_vertexset (G : pregraph)
  : isaprop (has_vertexset G)
  := isapropisaset (vertex G).

Definition has_edgesets (G : pregraph) : UU
  := ∏ x y : vertex G, isaset (edge G x y).

Lemma isaprop_has_edgesets (G : pregraph)
  : isaprop (has_edgesets G).
Proof.
  apply UniMath.CategoryTheory.Core.Categories.isaprop_has_homsets.
Qed.

(** ** Graphs. *)

Definition graph : UU
  := ∑ G : pregraph, has_vertexset G × has_edgesets G.

Definition make_graph (G : pregraph)
           (h : has_vertexset G)
           (k : has_edgesets G)
  : graph
  := G,, make_dirprod h k.

Definition pregraph_of_graph : graph → pregraph := pr1.
Coercion pregraph_of_graph : graph >-> pregraph.

Definition graph_has_vertexset (G : graph)
  : has_vertexset G
  := pr12 G.

Definition graph_has_edgesets (G : graph)
  : has_edgesets G
  := pr22 G.

(** ** Graph morphisms. *)

Definition graph_mor (G H : pregraph) : UU :=
  ∑ (f₀ : vertex G → vertex H),
  (∏ x y : vertex G, edge G x y → edge H (f₀ x) (f₀ y)).

Definition make_graph_mor {G H : pregraph}
  : ∏ (f₀ : vertex G → vertex H)
      (f₁ : ∏ x y : vertex G, edge G x y → edge H (f₀ x) (f₀ y)),
    graph_mor G H
  := tpair _.

Definition onvertex {G H : pregraph}
  : ∏ (p : graph_mor G H), vertex G → vertex H
  := pr1.

Definition onedge {G H : pregraph} (p : graph_mor G H) {x y : vertex G}
  : edge G x y → edge H (onvertex p x) (onvertex p y)
  := pr2 p x y.

Definition graph_mor_id (G : pregraph)
  : graph_mor G G
    := make_graph_mor
         (idfun (vertex G))
         (λ x y : vertex G, idfun (edge G x y)).

Definition graph_mor_comp {G H K: pregraph}
           (p : graph_mor G H) (q : graph_mor H K)
  : graph_mor G K
  := make_graph_mor
       (onvertex q ∘ onvertex p)
         (λ (x y : vertex G) (f : edge G x y), onedge q (pr2 p x y f)).

Lemma make_graph_mor_eq {G H : pregraph}
      (p₀ : vertex G → vertex H)
      (p₁ p₁' : ∏ x y : vertex G, edge G x y → edge H (p₀ x) (p₀ y))
      (e : ∏ x y (f : edge G x y), p₁ x y f = p₁' x y f)
  : make_graph_mor p₀ p₁ = make_graph_mor p₀ p₁'.
Proof.
  apply pair_path_in2.
  apply funextsec. intro x.
  apply funextsec. intro y.
  apply funextfun. intro f.
  apply e.
Defined.

Lemma graph_mor_id_left {G H : pregraph} (p : graph_mor G H) :
  graph_mor_comp (graph_mor_id G) p = p.
Proof.
  induction p as (p₀,p₁).
  apply make_graph_mor_eq.
  intros. apply idpath.
Defined.

Lemma graph_mor_id_right {G H : pregraph} (p : graph_mor G H) :
  graph_mor_comp p (graph_mor_id H) = p.
Proof.
  induction p as (p₀,p₁).
  apply make_graph_mor_eq.
  intros. apply idpath.
Defined.

Lemma graph_mor_comp_assoc {G1 G2 G3 G4 : pregraph}
      (p : graph_mor G1 G2) (q : graph_mor G2 G3) (r : graph_mor G3 G4)
  : graph_mor_comp p (graph_mor_comp q r) =
    graph_mor_comp (graph_mor_comp p q) r.
Proof.
  induction p as (p₀,p₁).
  induction q as (q₀,q₁).
  induction r as (r₀,r₁).
  apply make_graph_mor_eq.
  intros. apply idpath.
Qed.

Lemma isaset_graph_mor {G H : pregraph}
      (h : has_vertexset H) (k : has_edgesets H)
  : isaset (graph_mor G H).
Proof.
  apply isaset_total2.
  - exact (funspace_isaset h).
  - intro p₀.
    apply impred_isaset. intro x.
    apply impred_isaset. intro y.
    apply funspace_isaset.
    apply k.
Qed.

Definition graph_mor_eq {G H : pregraph} (p q : graph_mor G H)
           (e₀ : ∏ x : vertex G, onvertex p x = onvertex q x)
           (e₁ : ∏ x y (f : edge G x y),
                 UniMath.CategoryTheory.Core.Univalence.double_transport
                   (e₀ x) (e₀ y) (onedge p f) =
                 onedge q f)
  : p = q
  := UniMath.CategoryTheory.Core.Functors.functor_data_eq G H p q e₀ e₁.
