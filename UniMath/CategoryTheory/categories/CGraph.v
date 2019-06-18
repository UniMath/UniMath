(* ******************************************************************************* *)
(** * Category of correspondence graphs

    Marco Maggesi
    June 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.CGraph.

(** ** Precategory of precgraphs. *)

Definition precgraph_precategory_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor precgraph cgraph_mor.

Definition precgraph_precategory_data : precategory_data
  := make_precategory_data
       precgraph_precategory_ob_mor
       cgraph_mor_id
       (@cgraph_mor_comp).

Lemma is_precategory_precgraph : is_precategory precgraph_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  apply make_dirprod.
  repeat apply make_dirprod; cbn.
  - exact @cgraph_mor_id_left.
  - exact @cgraph_mor_id_right.
  - apply @cgraph_mor_comp_assoc.
Qed.

Definition precgraph_category : precategory
  := make_precategory
       precgraph_precategory_data
       is_precategory_precgraph.


(** ** Category of cgraphs. *)

Definition cgraph_precategory_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor cgraph cgraph_mor.

Definition cgraph_precategory_data : precategory_data
  := make_precategory_data
       cgraph_precategory_ob_mor
       (λ G : cgraph, cgraph_mor_id G)
       (λ G H K : cgraph, @cgraph_mor_comp G H K).

Lemma is_precategory_cgraph : is_precategory cgraph_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply make_dirprod; cbn.
  - exact @cgraph_mor_id_left.
  - exact @cgraph_mor_id_right.
  - exact @cgraph_mor_comp_assoc.
Qed.

Definition cgraph_precategory : precategory
  := make_precategory
       cgraph_precategory_data
       is_precategory_cgraph.

Lemma has_homsets_graph : has_homsets cgraph_precategory_ob_mor.
Proof.
  intros G H.
  apply isaset_cgraph_mor.
  - exact (isaset_node H).
  - exact (isaset_arc H).
Defined.

Definition cgraph_category : precategory
  := make_precategory
       cgraph_precategory_data
       is_precategory_cgraph.
