(* ******************************************************************************* *)
(** * Bicategory of graphs
    Benedikt Ahrens, Marco Maggesi
    May 2018
    Revised June 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.PartB.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.Graph.

(** NB: pregraph is the same as precategory_ob_mor. *)

Require UniMath.CategoryTheory.Core.Univalence.  (* double_transport *)
Require UniMath.CategoryTheory.Core.Functors.    (* functor_data_eq *)

(** Should be moved in Combinatorics/Graph.v,
    but it depends on code from CategoryTheory for now. *)
Definition graph_mor_eq {G H : pregraph} (p q : graph_mor G H)
           (e₀ : ∏ x : vertex G, onvertex p x = onvertex q x)
           (e₁ : ∏ x y (f : edge G x y),
                 UniMath.CategoryTheory.Core.Univalence.double_transport
                   (e₀ x) (e₀ y) (onedge p f) =
                 onedge q f)
  : p = q
  := UniMath.CategoryTheory.Core.Functors.functor_data_eq G H p q e₀ e₁.

Lemma isaprop_has_edgesets (G : pregraph)
  : isaprop (has_edgesets G).
Proof.
  apply UniMath.CategoryTheory.Core.Categories.isaprop_has_homsets.
Qed.

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
  - exact @graph_mor_id_left.
  - exact @graph_mor_id_right.
  - exact @graph_mor_comp_assoc.
Qed.

Definition graph_precategory : precategory
  := make_precategory
       graph_precategory_data
       is_precategory_graph.

Lemma has_homsets_graph : has_homsets graph_precategory_ob_mor.
Proof.
  intros G H.
  apply isaset_graph_mor.
  - exact (graph_has_vertexset H).
  - exact (graph_has_edgesets H).
Defined.
