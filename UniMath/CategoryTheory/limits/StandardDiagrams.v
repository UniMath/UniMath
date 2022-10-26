
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

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

  (* Two verticies (● 0) and (● 1), and two parallell edges (inl tt) and (inr tt) *)
  Definition pair_graph : graph.
  Proof.
    use make_graph.
    - exact(⟦ 2 ⟧).
    - apply(two_rec (two_rec empty (unit ⨿ unit))).
      exact(λ _, empty).
  Defined.

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

  Definition make_pair_diagram {C : category}
    (a b : C)
    (f g : a --> b)
    : diagram pair_graph C.
  Proof.
    use make_diagram.
    - exact(two_rec a b).
    - use two_rec_dep; use two_rec_dep; try exact(empty_rect _).
      exact(sumofmaps (λ _, f) (λ _, g)).
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

  Definition make_discrete_cocone {J : category}
    {X : UU}
    (d : diagram (discrete_graph X) J)
    (z : J)
    (f : ∏ (x : X), J⟦dob d x, z⟧)
    : cocone d z.
  Proof.
    use make_cocone.
    - exact f.
    - exact(λ _ _, empty_rect _).
  Defined.

  Definition make_parallell_cocone {J : category}
    {X : UU}
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

  Definition make_multispan_cocone {J : category} {X : UU}
    (d : diagram (multispan_graph X) J)
    (apex : J)
    (base_inject : J⟦ dob d (inr tt), apex ⟧)
    (inject : ∏ (x : X), J⟦ dob d (inl x), apex ⟧)
    (commutes : ∏ (x : X), @dmor _ _ d (inr tt) (inl x) tt · inject x = base_inject)
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
