
(** ***********************************************************************
 *   Filtered Categories                                                  *
 *                                                                        *
 *     Definition of filtered categories and compact/finitely presentable *
 *     objects. Two definitions of filtered categories are given,         *
 *              [is_filtered]                                             *
 *              [is_filtered_alt]                                         *
 *     and a proof that they are equivalent is given in [weq_filtered].   *
 *                                                                        *
 *     Contents                                                           *
 *     1) Filtered categories                                             *
 *     2) Compact objects                                                 *
 *     3) Properties                                                      *
 *     4) Equivalence between [is_filtered] and [is_filtered_alt].        *
 *                                                                        *
 *************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.covyoneda.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.

Require Import UniMath.CategoryTheory.limits.StandardDiagrams.

Local Open Scope cat.
Local Open Scope stn.

Section filtered_categories.
  (**
   1. A category is filtered if it admits cocones for every diagram of
      finite graphs, or equivalently if it admits cocones for diagrams
      of the empty graph, the two-point graph and the graph with two
      parallell edges.
   *)

  Definition is_filtered (J : category) : UU
    := ∏ (g : graph)
         (d : diagram g J),
      (is_finite_graph g) -> ∥ ∑ (z : J), cocone d z ∥.

  Definition is_filtered_alt
    (J : category)
    : UU
    := ∥ J ∥
         × (∏ (d : diagram bool_graph J), ∃ z : J, cocone d z)
         × (∏ (d : diagram pair_graph J), ∃ z : J, cocone d z).

  Definition preserves_filtered_colimits {C D : category} (F : functor C D) : UU
    := ∏ (J : category),
      is_filtered J -> preserves_colimits_of_shape F J.

End filtered_categories.


Section compact.

  (**
   2. Compact / finitely presentable objects.
   *)

  Definition hom {C : category} (x : C) : C ⟶ SET
  := (covyoneda C x).

  Definition is_compact {C : category} (x : C) : UU
    := preserves_filtered_colimits (hom x).

End compact.

Section properties.

  (**
   3. Properties.
   *)

  Lemma isaprop_is_filtered {J : category}
    : isaprop (is_filtered J).
  Proof.
    do 2 (apply impred_isaprop; intro).
    apply isapropimpl, propproperty.
  Qed.

  Lemma isaprop_is_filtered_alt {J : category}
    : isaprop (is_filtered_alt J).
  Proof.
    apply isapropdirprod;
      [apply propproperty
      |apply isapropdirprod;
       repeat (apply impred_isaprop; intro; try apply propproperty)].
  Qed.

  Lemma isaprop_iscompact {C : category} (X : C) : isaprop (is_compact X).
  Proof.
    do 6 (apply impred_isaprop ; intro).
    apply isaprop_isColimCocone.
  Qed.

End properties.

Section alternate_formulation.

  (**
    4. The equivalence between [is_filtered] and [is_filtered_alt].
   *)

  Lemma filtered_is_inhabited {J : category}
    (filtered : is_filtered J)
    : ∥ J ∥.
  Proof.
    exact(hinhfun pr1 (filtered empty_graph make_empty_diagram is_finite_graph_empty)).
  Qed.

  Lemma filtered_has_bool_cocones {J : category}
    (filtered : is_filtered J)
    (d : diagram bool_graph J)
    : ∃ z : J, cocone d z.
  Proof.
    exact(filtered bool_graph _ is_finite_graph_bool).
  Qed.

  Lemma filtered_has_pair_cocones {J : category}
    (filtered : is_filtered J)
    (d : diagram pair_graph J)
    : ∃ z : J, cocone d z.
  Proof.
    exact(filtered pair_graph d is_finite_graph_pair).
  Qed.

  (* The implication [is_filtered] -> [is_filtered_alt] is the easy one. *)

  Definition filtered_to_filtered_alt {J : category}
    (filtered : is_filtered J)
    : is_filtered_alt J.
  Proof.
    repeat split.
    - exact(filtered_is_inhabited filtered).
    - exact(filtered_has_bool_cocones filtered).
    - exact(filtered_has_pair_cocones filtered).
  Defined.

  Lemma filtered_alt_has_discrete_cocones_stn {J : category}
    (filtalt : is_filtered_alt J)
    (n : nat)
    (d : diagram (discrete_graph (⟦ n ⟧)) J)
    : ∃ z : J, cocone d z.
  Proof.
    destruct filtalt as [inhab [boolcc paircc]].
    induction n as [| n IHn].
    - use(hinhfun _ inhab).
      intro j. exists j.
      use make_discrete_cocone.
      exact(λ x : ⟦ 0 ⟧, fromempty (negstn0 x)).
    - set (d₁ := make_discrete_diagram (λ k : ⟦ n ⟧, dob d (dni lastelement k))).
      use(IHn d₁); intros [P Pcc].

      set (d₂ := make_bool_diagram P (dob d lastelement)).
      use(boolcc d₂); intros [Q Qcc]; apply hinhpr.

      exists Q.
      use make_discrete_cocone.
      + apply(weqonsecbase (λ (v : ⟦ S n ⟧), J ⟦ dob d v, Q ⟧) (weqdnicoprod n lastelement)).
        apply coprod_rect.
        * exact(λ k : ⟦ n ⟧, coconeIn Pcc k · coconeIn Qcc true).
        * apply unit_rect.
          exact(coconeIn Qcc false).
  Qed.

  Lemma filtered_alt_has_discrete_cocones {J : category}
    (filtalt : is_filtered_alt J)
    (X : UU)
    (d : diagram (discrete_graph X) J)
    (n : nat)
    (w : X ≃ ⟦ n ⟧)
    : ∃ z : J, cocone d z.
  Proof.
    use(filtered_alt_has_discrete_cocones_stn filtalt n).
    - exact(make_discrete_diagram (λ k : ⟦ n ⟧, dob d (invmap w k))).
    - intros [P Pcc]; apply hinhpr.
      exists P.
      use make_discrete_cocone.
      + intro x.
        apply(transportf
                (fun y : X => J⟦ dob d y, P ⟧)
                (homotinvweqweq w x)).
        exact(coconeIn Pcc (w x)).
  Qed.

  Definition filtered_alt_has_parallell_stn {J : category}
    (filtalt : is_filtered_alt J)
    (n : nat)
    (d : diagram (parallell_graph (⟦ n ⟧)) J)
    : ∃ z : J, cocone d z.
  Proof.
    destruct filtalt as [inhab [bool_cc pair_cc]].

    induction n as [|n IHn].
    - set (d₁ := make_bool_diagram (dob d parallell_start) (dob d parallell_end)).
      use(hinhfun _ (bool_cc d₁)); intros [P Pcc].
      exists P.
      use make_parallell_cocone.
      + exact(coconeIn Pcc true).
      + exact(coconeIn Pcc false).
      + exact(λ k : ⟦ 0 ⟧, fromempty (negstn0 k)).
    -
      (* dₙ is the restriction of d to ⟦ n ⟧ *)
      transparent assert(dₙ : (diagram (parallell_graph (⟦ n ⟧)) J)). {
        use make_parallell_diagram.
        - exact(dob d parallell_start).
        - exact(dob d parallell_end).
        - exact(λ k : ⟦ n ⟧, dmor d (parallell_edge (dni lastelement k))).
      }

      use(IHn dₙ); intros [Dₙ Dcc]. (* Dₙ/Dcc is the cocone over the parallell arrows {0, ..., n} *)
      transparent assert(pairing: (diagram pair_graph J)). {
        use make_pair_diagram.
        - exact(dob d parallell_start).
        - exact Dₙ.
        - exact(coconeIn Dcc parallell_start).
        - exact(dmor d (parallell_edge lastelement) · coconeIn Dcc parallell_end).
      }
      use(hinhfun _ (pair_cc pairing)); intros [Q Qcc].
      exists Q.
      use make_parallell_cocone.
      + exact(coconeIn Dcc parallell_start · coconeIn Qcc pair_dst).
      + exact(coconeIn Dcc parallell_end · coconeIn Qcc pair_dst).
      + apply(weqonsecbase _ (weqdnicoprod n lastelement)).
        apply coprod_rect.
        * intro.
          etrans;[apply assoc |].
          apply cancel_postcomposition.
          exact(parallell_cocone_commutes Dcc _).
        * apply unit_rect.
          etrans;[apply assoc |]. cbn.
          etrans;[exact(pair_cocone_commutes Qcc pair_right) |].
          exact(!pair_cocone_commutes Qcc pair_left).
  Qed.

  Lemma filtered_alt_has_parallell_cocones {J : category}
    (filtalt : is_filtered_alt J)
    (X : UU)
    (n : nat)
    (w : X ≃ ⟦ n ⟧)
    (d : diagram (parallell_graph X) J)
    : ∃ z : J, cocone d z.
  Proof.
    set (dₙ := make_parallell_diagram (⟦ n ⟧)
                 (dob d parallell_start)
                 (dob d parallell_end)
                 (λ k : ⟦ n ⟧, dmor d (parallell_edge (invmap w k)))).

    use(hinhfun _ (filtered_alt_has_parallell_stn filtalt n dₙ)).
    intros [P Pcc].
    exists P.
    use make_parallell_cocone.
    - exact(coconeIn Pcc parallell_start).
    - exact(coconeIn Pcc parallell_end).
    - apply(weqonsecbase _ (invweq w)).
      exact(λ k : ⟦ n ⟧, parallell_cocone_commutes Pcc k).
  Qed.

  Lemma filtered_alt_has_finite_multispan_cocones {J : category}
    (filtalt : is_filtered_alt J)
    (X : UU)
    (n : nat)
    (w : X ≃ ⟦ n ⟧)
    (d : diagram (multispan_graph X) J)
    : ∃ z : J, cocone d z.
  Proof.
    set (base := dob d multispan_base).

    set (point_diagram := make_discrete_diagram' d).

    assert(r : (X ⨿ unit) ≃ ⟦ (S n) ⟧). {
      use(weqcomp (weqcoprodf1 w)).
      exact(weqdnicoprod n lastelement).
    }

    use(filtered_alt_has_discrete_cocones filtalt _ point_diagram (S n) r).
    intros [P Pcc].

    transparent assert(edge_diagram : (diagram (parallell_graph (X ⨿ unit)) J)). {
      use make_parallell_diagram.
      - exact base.
      - exact P.
      - apply sumofmaps.
        * exact(λ x : X, dmor d (multispan_edge x) · (coconeIn Pcc (multispan_vertex x))).
        * exact(unit_rect _ (coconeIn Pcc multispan_base)).
    }

    use(filtered_alt_has_parallell_cocones filtalt (X ⨿ unit) (S n) r edge_diagram).
    intros [Q Qcc]; apply hinhpr.
    exists Q.
    use make_multispan_cocone.
    - exact(coconeIn Qcc parallell_start).
    - exact(λ x : X, coconeIn Pcc (multispan_vertex x) · coconeIn Qcc parallell_end).
    - intro x. etrans;[apply assoc |].
      exact(parallell_cocone_commutes Qcc (inl x)).
  Qed.

  Definition filtered_alt_to_filtered {J : category}
    (filtalt : is_filtered_alt J)
    : is_filtered J.
  Proof.
    intros g d gfinite.
    use (finite_vertexset gfinite); intros finitevert.
    set (n := pr1 finitevert).
    set (w := pr2 finitevert).
    set (finite_edges := finite_edgeset gfinite).

    (* Start by creating a point P above d with cocone injections, but no commutativity. *)
    set (points := make_discrete_diagram (dob d)).
    use(filtered_alt_has_discrete_cocones filtalt (vertex g) points n (invweq w)).
    intros [P Pcc].

    assert(edgechoice : ∥ ∏ (a b : vertex g), finstruct (edge a b) ∥). {
      do 2 (use(ischoicebasefiniteset (finite_vertexset gfinite)); intro).
      apply finite_edges.
    }
    use edgechoice; clear edgechoice.
    intros edgeset.

    transparent assert(ediagram : (∏ (a b : vertex g), diagram (parallell_graph ((edge a b) ⨿ unit)) J)).
    {
      intros a b.
      use(make_parallell_diagram _ (dob d a) P).
      apply sumofmaps.
      - exact(λ e, dmor d e · coconeIn Pcc b).
      - exact(unit_rect _ (coconeIn Pcc a)).
    }

    assert(D : (∏ (a b : vertex g), ∃ (Pab : J), cocone (ediagram a b) Pab)).
    {
      intros a b.
      set (k := pr1 (edgeset a b)).
      set (i := pr2 (edgeset a b)).
      use(filtered_alt_has_parallell_cocones filtalt ((edge a b) ⨿ unit) (S k)).
      refine(weqcomp _ (weqdnicoprod k lastelement)).
      exact(weqcoprodf1 (invweq i)).
    }

    assert(D' : ∥ (∏ (a b : vertex g), ∑ (Pab : J), cocone (ediagram a b) Pab) ∥). {
      do 2 (use(ischoicebasefiniteset (finite_vertexset gfinite)); intro).
      apply D.
    }

    (* For each pair (u, v) ∈ vertex g × vertex g there is an object D(u,v) in J,
       and a cocone over the diagram of (edges u v) composed with the injection
       into P. *)
    use D'; clear D'; clear D; intros D.

    transparent assert(spandiagram : (diagram (multispan_graph (vertex g × vertex g)) J)). {
      use make_multispan_diagram.
      - exact P.
      - intros [a b]. exact(pr1 (D a b)).
      - intros [a b]. exact(coconeIn (pr2 (D a b)) parallell_end).
    }

    (* The objects D(u, v) together with their cocone injections from P is a finite multi
       span. Since J is filtered there is a cocone [Q Qcc] over this span. *)

    use(filtered_alt_has_finite_multispan_cocones filtalt (vertex g × vertex g) (n * n)).
    - apply(weqcomp (invweq (weqdirprodf w w))).
      apply weqfromprodofstn.
    - exact spandiagram.
    - intros [Q Qcc]; apply hinhpr.

      (* Using Q together with the cocones D(u,v) and P to construct a cocone over d
         with apex Q. *)
      exists Q.
      use make_cocone.
      + exact(λ v : vertex g, coconeIn Pcc v · coconeIn Qcc multispan_base).
      + intros u v e.

        etrans. {
          apply maponpaths; apply maponpaths.
          exact(!multispan_cocone_commutes Qcc (u ,, v)).
        }

        etrans;[apply assoc |].
        etrans;[apply assoc |].
        set (Duv := pr2 (D u v)).

        etrans. { apply maponpaths_2. exact(parallell_cocone_commutes Duv (inl e)). }
        etrans. { apply maponpaths_2. exact(!parallell_cocone_commutes Duv (inr tt)). }

        etrans;[apply assoc'|].
        apply cancel_precomposition.
        exact(multispan_cocone_commutes Qcc (u ,, v)).
  Qed.

  Definition weq_filtered (J : category)
    : is_filtered J ≃ is_filtered_alt J.
  Proof.
    use weqimplimpl.
    - exact filtered_to_filtered_alt.
    - exact filtered_alt_to_filtered.
    - exact isaprop_is_filtered.
    - exact isaprop_is_filtered_alt.
  Defined.

End alternate_formulation.
