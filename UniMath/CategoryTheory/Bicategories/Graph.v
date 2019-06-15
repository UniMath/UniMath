(* ******************************************************************************* *)
(** * Bicategory of graphs
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors. (* functor_data_eq *)
Require Import UniMath.CategoryTheory.Core.Univalence. (* double_transport *)

(** ** Pregraphs. *)

Definition pregraph : UU
  := ∑ N : UU, N → N → UU.

Definition make_pregraph
  : ∏ N : UU, (N → N → UU) → pregraph
  := tpair _.

Definition node : pregraph → UU := pr1.
(* Coercion node : Graph >-> UU. *)

Definition edge : ∏ G : pregraph, node G → node G → UU := pr2.

Definition has_nodeset (G : pregraph) : UU
  := isaset (node G).

Definition isaprop_has_nodeset (G : pregraph)
  : isaprop (has_nodeset G)
  := isapropisaset (node G).

Definition has_edgesets (G : pregraph) : UU
  := ∏ x y : node G, isaset (edge G x y).

Lemma isaprop_has_edgesets (G : pregraph)
  : isaprop (has_edgesets G).
Proof.
  apply isaprop_has_homsets.
Qed.

(** ** Graphs. *)

Definition graph : UU
  := ∑ G : pregraph, has_nodeset G × has_edgesets G.

Definition make_graph (G : pregraph)
           (h : has_nodeset G)
           (k : has_edgesets G)
  : graph
  := G,, make_dirprod h k.

Definition pregraph_of_graph : graph → pregraph := pr1.
Coercion pregraph_of_graph : graph >-> pregraph.

Definition graph_has_nodeset (G : graph)
  : has_nodeset G
  := pr12 G.

Definition graph_has_edgesets (G : graph)
  : has_edgesets G
  := pr22 G.

(** ** Graph morphisms. *)

Definition graph_mor (G H : pregraph) : UU :=
  ∑ (f₀ : node G → node H),
  (∏ x y : node G, edge G x y → edge H (f₀ x) (f₀ y)).

Definition make_graph_mor {G H : pregraph}
  : ∏ (f₀ : node G → node H)
      (f₁ : ∏ x y : node G, edge G x y → edge H (f₀ x) (f₀ y)),
    graph_mor G H
  := tpair _.

Definition onnode {G H : pregraph}
  : ∏ (p : graph_mor G H), node G → node H
  := pr1.

Definition onedge {G H : pregraph} (p : graph_mor G H) {x y : node G}
  : edge G x y → edge H (onnode p x) (onnode p y)
  := pr2 p x y.

Definition graph_mor_id (G : pregraph)
  : graph_mor G G
    := make_graph_mor
         (idfun (node G))
         (λ x y : node G, idfun (edge G x y)).

Definition graph_mor_comp {G H K: pregraph}
           (p : graph_mor G H) (q : graph_mor H K)
  : graph_mor G K
  := make_graph_mor
       (onnode q ∘ onnode p)
         (λ (x y : node G) (f : edge G x y), onedge q (pr2 p x y f)).

Lemma make_graph_mor_eq {G H : pregraph}
      (p₀ : node G → node H)
      (p₁ p₁' : ∏ x y : node G, edge G x y → edge H (p₀ x) (p₀ y))
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
      (h : has_nodeset H) (k : has_edgesets H)
  : isaset (graph_mor G H).
Proof.
  apply isaset_total2.
  - apply funspace_isaset.
    exact h.
  - intro p₀.
    apply impred_isaset. intro x.
    apply impred_isaset. intro y.
    apply funspace_isaset.
    apply k.
Qed.

Definition graph_mor_eq {G H : pregraph} (p q : graph_mor G H)
           (e₀ : ∏ x : node G, onnode p x = onnode q x)
           (e₁ : ∏ x y (f : edge G x y),
                 double_transport (e₀ x) (e₀ y) (onedge p f) = onedge q f)
  : p = q
  := functor_data_eq G H p q e₀ e₁.

(** ** Precategory of pregraphs. *)

Definition pregraph_precategory_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor pregraph graph_mor.

Definition pregraph_precategory_data : precategory_data
  := make_precategory_data
       pregraph_precategory_ob_mor
       graph_mor_id
       (@graph_mor_comp).

Lemma is_precategory_pregraph : is_precategory pregraph_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply make_dirprod; cbn.
  - exact @graph_mor_id_left.
  - exact @graph_mor_id_right.
  - apply @graph_mor_comp_assoc.
Qed.

Definition pregraph_category : precategory
  := make_precategory
       pregraph_precategory_data
       is_precategory_pregraph.

(** ** Category of graphs. *)

Definition graph_precategory_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor graph graph_mor.

Definition graph_precategory_data : precategory_data
  := make_precategory_data
       graph_precategory_ob_mor
       (λ G : graph, graph_mor_id G)
       (λ G H K : graph, graph_mor_comp).

Lemma is_precategory_graph : is_precategory graph_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply make_dirprod; cbn.
  - intros G H. apply graph_mor_id_left.
  - intros G H. apply graph_mor_id_right.
  - intros G H K L. apply graph_mor_comp_assoc.
Qed.

Definition graph_precategory : precategory
  := make_precategory
       graph_precategory_data
       is_precategory_graph.

Lemma has_homsets_graph : has_homsets graph_precategory_ob_mor.
Proof.
  intros G H.
  apply isaset_graph_mor.
  - exact (graph_has_nodeset H).
  - exact (graph_has_edgesets H).
Defined.
