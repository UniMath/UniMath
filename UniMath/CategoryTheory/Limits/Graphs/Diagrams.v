
(** *************************************************

Contents:

- Definitions of graphs and diagrams

Written by Benedikt Ahrens and Anders Mörtberg, 2015-2016

*****************************************************)

Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

(** Definition of graphs and diagrams *)
Section diagram_def.

Definition graph := ∑ (D : UU), D -> D -> UU.

Definition vertex : graph -> UU := pr1.
Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g.

Definition make_graph (D : UU) (e : D → D → UU) : graph := tpair _ D e.

Definition diagram (g : graph) (C : precategory) : UU :=
  ∑ (f : vertex g -> C), ∏ (a b : vertex g), edge a b -> C⟦f a, f b⟧.

Definition make_diagram {g : graph} {C : precategory}
  (f : vertex g -> C)
  (P : (∏ (a b : vertex g),
         edge a b -> C⟦f a, f b⟧))
  : diagram g C
  := (f ,, P).

Definition dob {g : graph} {C : precategory} (d : diagram g C) : vertex g -> C :=
  pr1 d.

Definition dmor {g : graph} {C : precategory} (d : diagram g C) :
  ∏ {a b}, edge a b -> C⟦dob d a,dob d b⟧ := pr2 d.

Section diagram_from_functor.

Variables (J C : precategory).
Variable (F : functor J C).

Definition graph_from_precategory : graph :=  (pr1 (pr1 J)).

Definition diagram_from_functor : diagram graph_from_precategory C :=
  tpair _ _ (pr2 (pr1 F)).

End diagram_from_functor.

Definition constant_diagram
  {C : category}
  (J : graph)
  (c : C)
  : diagram J C
  := make_diagram (λ _, c) (λ _ _ _, identity c).

End diagram_def.

Coercion graph_from_precategory : precategory >-> graph.

Definition diagram_pointwise {A C : category} {g : graph} (D : diagram g [A, C]) (a : A) : diagram g C.
Proof.
exists (λ v, pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Section map.

Context {C D : precategory} (F : functor C D).

Definition mapdiagram {g : graph} (d : diagram g C) : diagram g D.
Proof.
use tpair.
- intros n; apply (F (dob d n)).
- simpl; intros m n e.
  apply (# F (dmor d e)).
Defined.

End map.

Section ConnectedGraphs.

Definition graph_zig_zag_of_length
           {g : graph}
           (n : nat)
  : ∏ (x y : vertex g), UU.
Proof.
  induction n as [ | n IHn ].
  - exact (λ x y, x = y).
  - exact (λ x y, ∑ (z : vertex g), ((edge x z) ⨿ (edge z x)) × IHn z y).
Defined.

Definition graph_zig_zag
          {g : graph}
          (x y : vertex g)
  : UU
  := ∑ (n : nat), graph_zig_zag_of_length n x y.

Definition length_of_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : nat
  := pr1 gs.

Definition empty_graph_zig_zag
           {g : graph}
           (x : vertex g)
  : graph_zig_zag x x
  := 0 ,, idpath x.

Definition left_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge x z)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inl f ,, pr2 gs)).

Definition right_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge z x)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inr f ,, pr2 gs)).

Definition append_graph_zig_zag_of_length
           {g : graph}
           {n m : nat}
           {x y z : vertex g}
           (fs : graph_zig_zag_of_length n x y)
           (gs : graph_zig_zag_of_length m y z)
  : graph_zig_zag_of_length (n + m) x z.
Proof.
  revert x y z fs gs.
  induction n as [ | n IHn ].
  - intros x y z fs gs.
    rewrite fs.
    exact gs.
  - intros x y z fs gs.
    induction fs as [ w fs ].
    induction fs as [ f fs ].
    induction f as [ f | f ].
    + exact (w ,, inl f ,, IHn w y z fs gs).
    + exact (w ,, inr f ,, IHn w y z fs gs).
Defined.

Definition append_graph_zig_zag
           {g : graph}
           {x y z : vertex g}
           (fs : graph_zig_zag x y)
           (gs : graph_zig_zag y z)
  : graph_zig_zag x z
  := length_of_graph_zig_zag fs + length_of_graph_zig_zag gs
     ,,
     append_graph_zig_zag_of_length (pr2 fs) (pr2 gs).

Definition post_cons_left_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge y z)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inl f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition post_cons_right_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge z y)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inr f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition reverse_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y : vertex g}
           (gs : graph_zig_zag_of_length n x y)
  : graph_zig_zag_of_length n y x.
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (pathsinv0 gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (post_cons_right_graph_zig_zag_of_length (IHn _ _ gs) g').
    + exact (post_cons_left_graph_zig_zag_of_length (IHn _ _ gs) g').
Defined.

Definition reverse_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : graph_zig_zag y x
  := length_of_graph_zig_zag gs ,, reverse_graph_zig_zag_of_length (pr2 gs).

(* this assumes the induction hypothesis for all
   edges, not just those in the path *)
Lemma graph_zig_zag_strong_induction_helper
    {g : graph}
    {P : vertex g -> UU} :
  ∏ n, ∏ (x y : vertex g),
      (P x) ->
      (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
      graph_zig_zag_of_length n x y ->
      P y.
Proof.
  intro n.
  induction n as [|n Hn].
  - intros x y Hx _ gs.
    now rewrite <- gs.
  - intros x y Hx eind gs.
    destruct gs as [z [xz gs]].
    use (Hn _ _ _ eind gs).
    exact (eind x z Hx xz).
Defined.

Lemma graph_zig_zag_strong_induction
    {g : graph}
    {x y : vertex g}
    (gs : graph_zig_zag x y) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  intros P Hx Hind.
  destruct gs as [n gs].
  use graph_zig_zag_strong_induction_helper.
  - exact n.
  - exact x.
  - exact Hx.
  - exact Hind.
  - exact gs.
Defined.

Definition is_connected (g : graph) : UU :=
    ∏ (v1 v2 : vertex g), graph_zig_zag v1 v2.

Lemma connected_graph_zig_zag_strong_induction
    {g : graph}
    (x : vertex g)
    {y : vertex g}
    (H : is_connected g) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  apply graph_zig_zag_strong_induction.
  apply H.
Defined.

Lemma connected_graph_zig_zag_strong_induction_symmetric
    {g : graph}
    (x : vertex g)
    {y : vertex g}
    (H : is_connected g)
    (P : vertex g -> UU)
    (Hsymm : ∏ [a b : vertex g], edge b a -> (edge a b -> P b) -> P b) :
  (P x) ->
    (∏ (a b : vertex g), P a -> edge a b -> P b) ->
  P y.
Proof.
  intros Px IHn.
  apply (connected_graph_zig_zag_strong_induction x H P Px).
  intros a b Pa e.
  destruct e.
  - apply (IHn a b Pa e).
  - apply (Hsymm a b e).
    intro e'.
    apply (IHn a b Pa e').
Defined.

Lemma is_connected_pointed (g : graph) (v0 : vertex g) :
    (∏ (v : vertex g), graph_zig_zag v0 v) ->
        is_connected g.
Proof.
  intro H.
  intros v1 v2.
  use (append_graph_zig_zag (y := v0)).
  - exact (reverse_graph_zig_zag (H v1)).
  - exact (H v2).
Defined.

End ConnectedGraphs.


Section ProductGraph.
  Context {C : category}.

  Definition product_graph
    (g1 g2 : graph)
    : graph.
  Proof.
    use make_graph.
    - exact (vertex g1 × vertex g2).
    - intros (u1, u2) (v1, v2); exact (edge u1 v1 ⨿ edge u2 v2).
  Defined.

  Section FixADiagram.
    Context (g1 g2 : graph).
    Context (d : diagram (product_graph g1 g2) C).

    Definition product_diagram_pr1 (u2 : vertex g2) : diagram g1 C.
    Proof.
      use make_diagram.
      - intro u1; exact (dob d (u1 ,, u2)).
      - intros u1 v1 e1; refine (dmor d _); exact (inl e1).
    Defined.
    
    Definition product_diagram_pr2 (u1 : vertex g1) : diagram g2 C.
    Proof.
      use make_diagram.
      - intro u2; exact (dob d (u1 ,, u2)).
      - intros u2 v2 e2; refine (dmor d _); exact (inr e2).
    Defined.
  End FixADiagram.

  Definition product_diagram_coherence_law 
    {g1 g2 : graph} (d : diagram (product_graph g1 g2) C)
    := ∏ (u v : vertex g1) (u' v' : vertex g2) (e : edge u v) (e' : edge u' v'),
      dmor d (inr e' : edge (g := product_graph _ _) (u ,, u') (u ,, v')) 
        · dmor d (inl e : edge (g := product_graph _ _) (u ,, v') (v ,, v')) 
      = dmor d (inl e : edge (g := product_graph _ _) (u ,, u') (v ,, u')) 
        · dmor d (inr e' : edge (g := product_graph _ _) (v ,, u') (v ,, v')).

  Lemma isaprop_product_diagram_coherence_law
    {g1 g2 : graph} (d : diagram (product_graph g1 g2) C)
    : isaprop (product_diagram_coherence_law d).
  Proof.
    do 6 (use impred_isaprop; intro).
    use homset_property.
  Qed.

  Definition make_product_diagram 
    (g1 g2 : graph)
    (f : vertex g1 → vertex g2 → C)
    (P1 : ∏ u1 v1 u2 v2 (e1 : edge u1 v1), C⟦f u1 u2, f v1 v2⟧)
    (P2 : ∏ u1 v1 u2 v2 (e2 : edge u2 v2), C⟦f u1 u2, f v1 v2⟧)
    : diagram (product_graph g1 g2) C.
  Proof.
    use make_diagram.
    - intros (u1, u2); exact (f u1 u2).
    - intros (u1, u2) (v1, v2) [e1 | e2].
      + exact (P1 u1 v1 u2 v2 e1).
      + exact (P2 u1 v1 u2 v2 e2).
  Defined.

  Definition product_diagram_swap
    (g1 g2 : graph)
    (d : diagram (product_graph g1 g2) C)
    : diagram (product_graph g2 g1) C.
  Proof.
    use make_product_diagram.
    - intros u2 u1; use (dob d (u1 ,, u2)).
    - intros u2 v2 u1 v1 e2; refine (dmor d _); exact (inr e2).
    - intros u2 v2 u1 v1 e1; refine (dmor d _); exact (inl e1).
  Defined.
End ProductGraph.
