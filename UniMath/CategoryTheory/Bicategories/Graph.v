(* ******************************************************************************* *)
(** * Bicategory of graphs
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors. (* functor_data_eq *)
Require Import UniMath.CategoryTheory.Core.Univalence.

Section Graph.

Definition pregraph : UU := ∑ A : UU, A → A → UU.
Coercion node (G : pregraph) : UU := pr1 G.

Definition edge (G : pregraph) (a b : G) : UU := pr2 G a b.

Definition graph_mor (G1 G2 : pregraph) : UU
  := ∑ f0 : G1 → G2, ∏ (a b : G1), edge G1 a b → edge G2 (f0 a) (f0 b).

Definition mk_graph_mor (G1 G2 : pregraph) (f0 : G1 → G2)
           (f1 : ∏ (a b : G1), edge G1 a b → edge G2 (f0 a) (f0 b))
  : graph_mor G1 G2
  := f0,, f1.

Definition graph_mor_node {G1 G2 : pregraph} (f : graph_mor G1 G2) (a : G1) : G2
  := pr1 f a.
Coercion graph_mor_node : graph_mor >-> Funclass.

Definition graphmap {G1 G2 : pregraph} (f : graph_mor G1 G2) {a b : G1} (p : edge G1 a b)
  : edge G2 (f a) (f b)
  := pr2 f a b p.

Definition graph_mor_id (G : pregraph) : graph_mor G G
  := mk_graph_mor G G (idfun G) (λ a b : G, idfun (edge G a b)).

Definition graph_mor_comp {G1 G2 G3 : pregraph} (f : graph_mor G1 G2) (g : graph_mor G2 G3)
  : graph_mor G1 G3
  := mk_graph_mor G1 G3
                  (g ∘ f)%functions
                  (λ (a b : G1) (p : edge G1 a b), graphmap g (graphmap f p)).

Definition graph_mor_eq G1 G2 (f g : graph_mor G1 G2)
      (e0 : ∏ a, f a = g a)
      (e1 : ∏ a b (p : edge G1 a b),
              double_transport (e0 a) (e0 b) (graphmap f p) = graphmap g p)
  : f = g
  := functor_data_eq G1 G2 f g e0 e1.

Lemma graph_mor_id_right (G1 G2 : pregraph) (f : graph_mor G1 G2)
  : graph_mor_comp (graph_mor_id G1) f = f.
Proof.
  use graph_mor_eq; intros; apply idpath.
Qed.

Lemma graph_mor_id_left (G1 G2 : pregraph) (f : graph_mor G1 G2)
  : graph_mor_comp f (graph_mor_id G2) = f.
Proof.
  use graph_mor_eq; intros; apply idpath.
Qed.

Lemma graph_mor_comp_assoc (G1 G2 G3 G4 : pregraph)
      (f : graph_mor G1 G2) (g : graph_mor G2 G3) (h : graph_mor G3 G4)
  :   graph_mor_comp f (graph_mor_comp g h)
    = graph_mor_comp (graph_mor_comp f g) h.
Proof.
  use graph_mor_eq; intros; apply idpath.
Qed.

Definition graph_ob_mor : precategory_ob_mor
  := pregraph,, graph_mor.

Definition graph_id_comp : precategory_id_comp graph_ob_mor
  := graph_mor_id,, @graph_mor_comp.

Definition graph_precategory_data : precategory_data
  := graph_ob_mor,, graph_id_comp.

Lemma is_precategory_graph : is_precategory graph_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply dirprodpair; cbn.
  - apply graph_mor_id_right.
  - apply graph_mor_id_left.
  - apply graph_mor_comp_assoc.
Qed.

Definition graph_precategory : precategory
  := graph_precategory_data,, is_precategory_graph.

End Graph.