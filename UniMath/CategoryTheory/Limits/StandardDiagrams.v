
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.

Local Open Scope cat.
Local Open Scope stn.

(** * Standard graphs and diagrams.

    Contents
    1. Graphs
    2. Diagram constructors
    3. Cocone constructors

 *)

Section graphs.
  (**
   1. Graphs.
   *)

  Definition empty_graph : graph
    := make_graph empty (λ _ _, empty).

  Definition unit_graph : graph
    := make_graph unit (λ _ _, empty).

  (* The graph with two verticies, true and false, no edges. *)
  Definition bool_graph : graph
    := make_graph bool (λ _ _, empty).

    (* The interval graph: true ---tt---> false *)
  Definition interval_graph : graph.
  Proof.
    use make_graph.
    - exact bool.
    - intros a b.
      induction a; induction b.
      + exact empty.
      + exact unit.             (* true --> false *)
      + exact empty.
      + exact empty.
  Defined.

  (* (● 1) <------ (● 0) ------> (● 2) *)
  Definition span_graph : graph.
  Proof.
    use make_graph.
    - exact three.
    - use three_rec.
      + apply three_rec.
        * exact empty.
        * exact unit.
        * exact unit.
      + exact(λ _, empty).
      + exact(λ _, empty).
  Defined.

  (* X as verticies, no edges. *)
  Definition discrete_graph (X : UU) : graph
    := make_graph X (λ _ _, empty).


  (* The graph with two verticies: (● 0) and (● 1),
     and X as edges from (● 0) to (● 1), no other edges.

     Input \mdlgblkcircle for ●, or use (stnpr 0) and (stnpr 1) *)

  Definition parallell_graph (X : UU) : graph.
  Proof.
    use make_graph.
    - exact two.
    - use two_rec_dep.
      + exact(two_rec empty X).
      + exact(λ _, empty).
  Defined.

  Definition parallell_start {X : UU}
    : vertex (parallell_graph X)
    := (● 0).

  Definition parallell_end {X : UU}
    : vertex (parallell_graph X)
    := (● 1).

  Definition parallell_edge {X : UU}
    (e : X)
    : @edge (parallell_graph X) parallell_start parallell_end
    := e.

  (* Two parallell edges, pair_left, pair_right : : pair_src --> pair_end. *)

  Definition pair_graph : graph
    := parallell_graph (unit ⨿ unit).

  Definition pair_src : vertex pair_graph
    := (● 0).

  Definition pair_dst : vertex pair_graph
    := (● 1).

  Definition pair_left : @edge pair_graph pair_src pair_dst
    := inl tt.

  Definition pair_right : @edge pair_graph pair_src pair_dst
    := inr tt.

  (* Multi span: One base vertex (inr tt) and X verticies
     with one unique edge from the base each, no other edges. *)
  Definition multispan_graph (X : UU) : graph.
  Proof.
    use make_graph.
    - exact(X ⨿ unit).          (* inr tt is the base point. *)
    - use coprod_rect.
      + exact(λ _ _, empty).    (* No edges x --> unit *)
      + apply unit_rect.
        apply coprod_rect.
        * exact(λ _, unit).     (* One edge unit --> x *)
        * exact(λ _, empty).    (* No edge unit --> unit *)
  Defined.

  Definition multispan_vertex {X : UU}
    (x : X)
    : vertex (multispan_graph X)
    := (inl x).

  Definition multispan_base {X : UU}
    : vertex (multispan_graph X)
    := (inr tt).

  Definition multispan_edge {X : UU}
    (x : X)
    : edge multispan_base (multispan_vertex x)
    := tt.

End graphs.

Section diagrams.
  (**
   2. Diagram constructors.
   *)

  Definition make_empty_diagram {C : category}
    : diagram empty_graph C
    := make_diagram
         (fromempty : vertex empty_graph -> C)
         (λ _ _, fromempty).

  Definition make_unit_diagram {C : category}
    (point : C)
    : diagram unit_graph C.
  Proof.
    use make_diagram.
    - exact(unit_rect _ point).
    - exact(λ _ _, empty_rect _).
  Defined.

  Definition make_bool_diagram {C : category}
    (a b : C)
    : diagram bool_graph C.
  Proof.
    use make_diagram.
    - exact(bool_rect _ a b).
    - intros *; exact fromempty.
  Defined.

  Definition make_interval_diagram {C : category}
    (x : C)
    (y : C)
    (f : x --> y)
    : diagram interval_graph C.
  Proof.
    use make_diagram.
    - exact(bool_rect _ x y).
    - intros a b; destruct a, b; try (exact fromempty).
      exact(λ _ , f).
  Defined.

  Definition make_span_diagram {C : category }
    (a b c : C)
    (f : C ⟦a, b⟧)
    (g : C⟦a, c⟧)
    : diagram span_graph C.
  Proof.
    use make_diagram.
    - exact(three_rec a b c).
    - use three_rec_dep; use three_rec_dep; try exact(empty_rect _).
      + exact(unit_rect _ f).
      + exact(unit_rect _ g).
  Defined.

  Definition make_discrete_diagram {J : category} {X : UU}
    (objects : X -> J)
    : diagram (discrete_graph X) J.
  Proof.
    use make_diagram.
    - exact objects.
    - exact(λ _ _, empty_rect _).
  Defined.

  (* Given any diagram we can obtain a new diagram, forgetting the edges in the original graph. *)
  Definition make_discrete_diagram' {J : category}
    {g : graph}
    (d : diagram g J)
    : diagram (discrete_graph (vertex g)) J.
  Proof.
    use make_diagram.
    - exact(dob d).
    - exact(λ _ _, empty_rect _).
  Defined.

  Definition make_parallell_diagram {C : category}
    (X : UU)
    (x y : C)
    (f : ∏ (t : X), x --> y)
    : diagram (parallell_graph X) C.
  Proof.
    use make_diagram.
    - exact(two_rec x y).
    - use two_rec_dep.
      + use(two_rec_dep _ (empty_rect _) f).
      + exact(λ _, empty_rect _).
  Defined.

  Definition make_pair_diagram {C : category}
    (a b : C)
    (f g : a --> b)
    : diagram pair_graph C.
  Proof.
    apply(make_parallell_diagram (unit ⨿ unit) a b).
    exact(sumofmaps (λ _, f) (λ _, g)).
  Defined.

  Definition make_multispan_diagram {J : category}
    (X : UU)
    (base : J)
    (endpoint : ∏ (x : X), J)
    (morphism : ∏ (x : X), J⟦ base, endpoint x ⟧)
    : diagram (multispan_graph X) J.
  Proof.
    use make_diagram.
    - exact(sumofmaps endpoint (λ _, base)).
    - use coprod_rect.
      + exact(λ _ _, empty_rect _).
      + apply unit_rect.
        use coprod_rect.
        * exact(λ (a : X) (_ : unit), morphism a).
        * exact(λ _, empty_rect _).
  Defined.
End diagrams.

Section cocones.

  (**
   3. Constructors of cocones.
   *)
  Definition make_empty_cocone {J : category}
    (d : diagram empty_graph J)
    (j : J)
    : cocone d j.
  Proof.
    use make_cocone.
    - exact(empty_rect _).
    - exact(λ _ _, empty_rect _).
  Defined.

  Definition make_discrete_cocone {J : category} {X : UU}
    (d : diagram (discrete_graph X) J)
    (z : J)
    (f : ∏ (x : X), J⟦dob d x, z⟧)
    : cocone d z.
  Proof.
    use make_cocone.
    - exact f.
    - exact(λ _ _, empty_rect _).
  Defined.

  Definition make_parallell_cocone {J : category} {X : UU}
    (d : diagram (parallell_graph X) J)
    (z : J)
    (in₀ : dob d (stnpr 0) --> z)
    (in₁ : dob d (stnpr 1) --> z)
    (commutes : ∏ (x : X), dmor d (x : @edge (parallell_graph X) (stnpr 0) (stnpr 1)) · in₁ = in₀)
    : cocone d z.
  Proof.
    use make_cocone.
    - exact(two_rec_dep _ in₀ in₁).
    - abstract(use(two_rec_dep _ (two_rec_dep _ (empty_rect _) commutes)); exact(λ _, empty_rect _)).
  Defined.

  Lemma parallell_cocone_commutes {J : category} {X : UU}
    {d : diagram (parallell_graph X) J}
    {j : J}
    (cc : cocone d j)
    (x : X)
    : dmor d (parallell_edge x) · coconeIn cc parallell_end = coconeIn cc parallell_start.
  Proof.
    exact(coconeInCommutes cc parallell_start parallell_end (parallell_edge x)).
  Qed.

  Definition make_pair_cocone {J : category} {X : UU}
    (d : diagram pair_graph J)
    (j : J)
    (src_in : J⟦dob d pair_src, j⟧)
    (dst_in : J⟦dob d pair_dst, j⟧)
    (com_left : dmor d pair_left · dst_in = src_in)
    (com_right : dmor d pair_right · dst_in = src_in)
    : cocone d j.
  Proof.
    use make_parallell_cocone.
    - exact src_in.
    - exact dst_in.
    - abstract(use coprod_rect; apply unit_rect; assumption).
  Defined.

  Lemma pair_cocone_commutes {J : category}
    {d : diagram pair_graph J}
    {j : J}
    (cc : cocone d j)
    (e : edge pair_src pair_dst)
    : dmor d e · coconeIn cc pair_dst = coconeIn cc pair_src.
  Proof.
    exact(coconeInCommutes cc pair_src pair_dst e).
  Qed.

  Definition make_multispan_cocone {J : category} {X : UU}
    (d : diagram (multispan_graph X) J)
    (apex : J)
    (base_inject : J⟦ dob d multispan_base, apex ⟧)
    (inject : ∏ (x : X), J⟦ dob d (multispan_vertex x), apex ⟧)
    (commutes : ∏ (x : X), dmor d (multispan_edge x) · inject x = base_inject)
    : cocone d apex.
  Proof.
    use make_cocone.
    - apply coprod_rect.
      + exact inject.
      + apply unit_rect.
        exact base_inject.
    - abstract(use coprod_rect; [exact(λ _ _, empty_rect _) | use unit_rect ];
               use coprod_rect; cbn; [exact(λ a, unit_rect _ (commutes a))
                                       |exact(λ _, empty_rect _)]).
  Defined.

  Lemma multispan_cocone_commutes {J : category} {X : UU}
    {d : diagram (multispan_graph X) J}
    {apex : J}
    (cc : cocone d apex)
    (z : X)
    : (dmor d (multispan_edge z)) · coconeIn cc (multispan_vertex z) =  coconeIn cc multispan_base.
  Proof.
    exact(coconeInCommutes cc multispan_base (multispan_vertex z) tt).
  Qed.

End cocones.

Section finite.
  Definition is_finite_graph (g : graph) : UU
    := isfinite (vertex g)
         × ∏ (a b : vertex g), isfinite (edge a b).

  Definition finite_vertexset {g : graph} (gfinite : is_finite_graph g)
    : isfinite (vertex g)
    := pr1 gfinite.

  Definition finite_edgeset {g : graph} (gfinite : is_finite_graph g)
    : ∏ (a b : vertex g), isfinite (edge a b)
    := pr2 gfinite.

  (* Proofs that some of the above graphs are finite. *)
  Lemma is_finite_graph_empty
    : is_finite_graph empty_graph.
  Proof.
    split.
    - exact isfiniteempty.
    - exact(λ _ _, isfiniteempty).
  Qed.

  Lemma is_finite_graph_unit
    : is_finite_graph unit_graph.
  Proof.
    split.
    - exact isfiniteunit.
    - exact(λ _ _, isfiniteempty).
  Qed.

  Lemma is_finite_graph_bool
    : is_finite_graph bool_graph.
  Proof.
    split.
    - exact isfinitebool.
    - exact(λ _ _, isfiniteempty).
  Qed.

  Lemma is_finite_graph_pair
    : is_finite_graph pair_graph.
  Proof.
    split.
    - exact(isfinitestn 2).
    - use two_rec_dep; use two_rec_dep; try exact isfiniteempty.
      apply isfinitecoprod; apply isfiniteunit.
  Qed.

  Lemma is_finite_graph_interval
    : is_finite_graph interval_graph.
  Proof.
    split.
    - exact isfinitebool.
    - use bool_rect; use bool_rect; try exact isfiniteempty.
      exact isfiniteunit.
  Qed.
End finite.
