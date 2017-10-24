(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Algebra.DivisionRig.
Require Import UniMath.Algebra.ConstructiveStructures.

Section Open.

Context {X : UU}.
Context (O : (X → hProp) → hProp).

Definition isSetOfOpen_union :=
  ∏ P : (X → hProp) → hProp,
    (∏ A : X → hProp, P A → O A) → O (union P).
Lemma isaprop_isSetOfOpen_union :
  isaprop isSetOfOpen_union.
Proof.
  apply (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Qed.
Definition isSetOfOpen_finite_intersection :=
  ∏ (P : Sequence (X → hProp)), (∏ m, O (P m)) → O (finite_intersection P).
Lemma isaprop_isSetOfOpen_finite_intersection :
  isaprop isSetOfOpen_finite_intersection.
Proof.
  apply (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Qed.

Definition isSetOfOpen_htrue :=
  O (λ _, htrue).

Definition isSetOfOpen_and :=
  ∏ A B, O A → O B → O (λ x, A x ∧ B x).
Lemma isaprop_isSetOfOpen_and :
  isaprop isSetOfOpen_and.
Proof.
  apply impred_isaprop ; intros A.
  apply impred_isaprop ; intros B.
  apply isapropimpl, isapropimpl.
  now apply propproperty.
Qed.

Lemma isSetOfOpen_hfalse :
  isSetOfOpen_union
  → O (λ _ : X, hfalse).
Proof.
  intros H0.
  rewrite <- union_hfalse.
  apply H0.
  intro.
  apply fromempty.
Qed.

Lemma isSetOfOpen_finite_intersection_htrue :
  isSetOfOpen_finite_intersection
  → isSetOfOpen_htrue.
Proof.
  intro H0.
  unfold isSetOfOpen_htrue.
  rewrite <- finite_intersection_htrue.
  apply H0.
  intros m.
  induction (nopathsfalsetotrue (pr2 m)).
Qed.

Lemma isSetOfOpen_finite_intersection_and :
  isSetOfOpen_finite_intersection
  → isSetOfOpen_and.
Proof.
  intros H0 A B Ha Hb.
  rewrite <- finite_intersection_and.
  apply H0.
  intros m ; simpl.
  induction m as [m Hm].
  now induction m.
Qed.
Lemma isSetOfOpen_finite_intersection_carac :
  isSetOfOpen_htrue
  → isSetOfOpen_and
  → isSetOfOpen_finite_intersection.
Proof.
  intros Htrue Hpair L.
  apply (pr2 (finite_intersection_hProp O)).
  split.
  - exact Htrue.
  - exact Hpair.
Qed.

Definition isSetOfOpen :=
  isSetOfOpen_union × isSetOfOpen_finite_intersection.

End Open.

Definition isTopologicalSet (X : UU) :=
  ∑ O : (X → hProp) → hProp, isSetOfOpen O.
Definition TopologicalSet := ∑ X : UU, isTopologicalSet X.

Definition mkTopologicalSet (X : UU) (O : (X → hProp) → hProp)
           (is : isSetOfOpen_union O)
           (is0 : isSetOfOpen_htrue O)
           (is1 : isSetOfOpen_and O) : TopologicalSet :=
  (X,,O,,is,,(isSetOfOpen_finite_intersection_carac _ is0 is1)).

Definition pr1TopologicatSet : TopologicalSet → UU := pr1.
Coercion pr1TopologicatSet : TopologicalSet >-> UU.

Definition isOpen {T : TopologicalSet} : (T → hProp) → hProp := pr1 (pr2 T).
Definition Open {T : TopologicalSet} :=
  ∑ O : T → hProp, isOpen O.
Definition pr1Open {T : TopologicalSet} : Open → (T → hProp) := pr1.
Coercion pr1Open : Open >-> Funclass.

Section Topology_pty.

Context {T : TopologicalSet}.

Lemma isOpen_union :
  ∏ P : (T → hProp) → hProp,
    (∏ A : T → hProp, P A → isOpen A)
    → isOpen (union P).
Proof.
  apply (pr1 (pr2 (pr2 T))).
Qed.
Lemma isOpen_finite_intersection :
  ∏ (P : Sequence (T → hProp)),
    (∏ m , isOpen (P m))
    → isOpen (finite_intersection P).
Proof.
  apply (pr2 (pr2 (pr2 T))).
Qed.

Lemma isOpen_hfalse :
  isOpen (λ _ : T, hfalse).
Proof.
  apply isSetOfOpen_hfalse.
  intros P H.
  now apply isOpen_union.
Qed.
Lemma isOpen_htrue :
  isOpen (λ _ : T, htrue).
Proof.
  rewrite <- finite_intersection_htrue.
  apply isOpen_finite_intersection.
  intros m.
  induction (nopathsfalsetotrue (pr2 m)).
Qed.
Lemma isOpen_and :
  ∏ A B : T → hProp,
    isOpen A → isOpen B → isOpen (λ x : T, A x ∧ B x).
Proof.
  apply isSetOfOpen_finite_intersection_and.
  intros P Hp.
  apply isOpen_finite_intersection.
  apply Hp.
Qed.
Lemma isOpen_or :
  ∏ A B : T → hProp,
    isOpen A → isOpen B → isOpen (λ x : T, A x ∨ B x).
Proof.
  intros A B Ha Hb.
  rewrite <- union_or.
  apply isOpen_union.
  intros C.
  apply hinhuniv.
  apply sumofmaps ; intros ->.
  exact Ha.
  exact Hb.
Qed.

End Topology_pty.

(** ** Neighborhood *)

Section Neighborhood.

Context {T : TopologicalSet}.

Definition neighborhood (x : T) : (T → hProp) → hProp :=
  λ P : T → hProp, ∃ O : Open, O x × (∏ y : T, O y → P y).

Lemma neighborhood_isOpen (P : T → hProp) :
  (∏ x, P x → neighborhood x P) <-> isOpen P.
Proof.
  split.
  - intros Hp.
    assert (H : ∏ A : T → hProp, isaprop (∏ y : T, A y → P y)).
    { intros A.
      apply impred_isaprop.
      intro y.
      apply isapropimpl.
      apply propproperty. }
    set (Q := λ A : T → hProp, isOpen A ∧ (hProppair (∏ y : T, A y → P y) (H A))).
    assert (X : P = (union Q)).
    { apply funextfun.
      intros x.
      apply hPropUnivalence.
      - intros Px.
        generalize (Hp _ Px).
        apply hinhfun.
        intros A.
        exists (pr1 A) ; split.
        split.
        apply (pr2 (pr1 A)).
        exact (pr2 (pr2 A)).
        exact (pr1 (pr2 A)).
      - apply hinhuniv.
        intros A.
        apply (pr2 (pr1 (pr2 A))).
        exact (pr2 (pr2 A)). }
    rewrite X.
    apply isOpen_union.
    intros A Ha.
    apply (pr1 Ha).
  - intros Hp x Px.
    apply hinhpr.
    exists (P,,Hp).
    split.
    exact Px.
    intros y Py.
    exact Py.
Qed.

Lemma neighborhood_imply :
  ∏ (x : T) (P Q : T → hProp),
    (∏ y : T, P y → Q y) → neighborhood x P → neighborhood x Q.
Proof.
  intros x P Q H.
  apply hinhfun.
  intros O.
  exists (pr1 O).
  split.
  - apply (pr1 (pr2 O)).
  - intros y Hy.
    apply H.
    apply (pr2 (pr2 O)).
    exact Hy.
Qed.
Lemma neighborhood_forall :
  ∏ (x : T) (P : T → hProp),
    (∏ y, P y) → neighborhood x P.
Proof.
  intros x P H.
  apply hinhpr.
  exists ((λ _ : T, htrue),,isOpen_htrue).
  split.
  easy.
  intros y _.
  now apply H.
Qed.
Lemma neighborhood_and :
  ∏ (x : T) (A B : T → hProp),
    neighborhood x A → neighborhood x B → neighborhood x (λ y, A y ∧ B y).
Proof.
  intros x A B.
  apply hinhfun2.
  intros Oa Ob.
  exists ((λ x, pr1 Oa x ∧ pr1 Ob x) ,, isOpen_and _ _ (pr2 (pr1 Oa)) (pr2 (pr1 Ob))).
  simpl.
  split.
  - split.
    + apply (pr1 (pr2 Oa)).
    + apply (pr1 (pr2 Ob)).
  - intros y Hy.
    split.
    + apply (pr2 (pr2 Oa)).
      apply (pr1 Hy).
    + apply (pr2 (pr2 Ob)).
      apply (pr2 Hy).
Qed.
Lemma neighborhood_point :
  ∏ (x : T) (P : T → hProp),
    neighborhood x P → P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros O.
  apply (pr2 (pr2 O)).
  apply (pr1 (pr2 O)).
Qed.

Lemma neighborhood_neighborhood :
  ∏ (x : T) (P : T → hProp),
    neighborhood x P
    → ∃ Q : T → hProp, neighborhood x Q
                        × ∏ y : T, Q y → neighborhood y P.
Proof.
  intros x P.
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  split.
  - apply (pr2 (neighborhood_isOpen _)).
    apply (pr2 (pr1 Q)).
    apply (pr1 (pr2 Q)).
  - intros y Qy.
    apply hinhpr.
    exists (pr1 Q).
    split.
    + exact Qy.
    + exact (pr2 (pr2 Q)).
Qed.

End Neighborhood.

Definition locally {T : TopologicalSet} (x : T) : Filter T.
Proof.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood x).
  - abstract (intros A B ;
              apply neighborhood_imply).
  - abstract (apply (pr2 (neighborhood_isOpen _)) ;
              [ apply isOpen_htrue |
                apply tt]).
  - abstract (intros A B ;
              apply neighborhood_and).
  - abstract (intros A Ha ;
              apply hinhpr ;
              exists x ;
              now apply neighborhood_point in Ha).
Defined.

(** ** Base of Neighborhood *)

Definition is_base_of_neighborhood {T : TopologicalSet} (x : T) (B : (T → hProp) → hProp) :=
  (∏ P : T → hProp, B P → neighborhood x P)
    × (∏ P : T → hProp, neighborhood x P → ∃ Q : T → hProp, B Q × (∏ t : T, Q t → P t)).

Definition base_of_neighborhood {T : TopologicalSet} (x : T) :=
  ∑ (B : (T → hProp) → hProp), is_base_of_neighborhood x B.
Definition pr1base_of_neighborhood {T : TopologicalSet} (x : T) :
  base_of_neighborhood x → ((T → hProp) → hProp) := pr1.
Coercion pr1base_of_neighborhood : base_of_neighborhood >-> Funclass.

Section base_default.

Context {T : TopologicalSet} (x : T).

Definition base_default : (T → hProp) → hProp :=
  λ P : T → hProp, isOpen P ∧ P x.

Lemma base_default_1 :
  ∏ P : T → hProp, base_default P → neighborhood x P.
Proof.
  intros P Hp.
  apply hinhpr.
  exists (P,,(pr1 Hp)) ; split.
  exact (pr2 Hp).
  easy.
Qed.
Lemma base_default_2 :
  ∏ P : T → hProp, neighborhood x P → ∃ Q : T → hProp, base_default Q × (∏ t : T, Q t → P t).
Proof.
  intros P.
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  repeat split.
  exact (pr2 (pr1 Q)).
  exact (pr1 (pr2 Q)).
  exact (pr2 (pr2 Q)).
Qed.

End base_default.

Definition base_of_neighborhood_default {T : TopologicalSet} (x : T) : base_of_neighborhood x.
Proof.
  exists (base_default x).
  split.
  - now apply base_default_1.
  - now apply base_default_2.
Defined.

Definition neighborhood' {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) : (T → hProp) → hProp :=
  λ P : T → hProp, ∃ O : T → hProp, B O × (∏ t : T, O t → P t).

Lemma neighborhood_equiv {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) :
  ∏ P, neighborhood' x B P <-> neighborhood x P.
Proof.
  split.
  - apply hinhuniv.
    intros O.
    generalize ((pr1 (pr2 B)) (pr1 O) (pr1 (pr2 O))).
    apply neighborhood_imply.
    exact (pr2 (pr2 O)).
  - intros Hp.
    generalize (pr2 (pr2 B) P Hp).
    apply hinhfun.
    intros O.
    exists (pr1 O).
    exact (pr2 O).
Qed.

(** ** Some topologies *)

(** *** Topology from neighborhood *)

Definition isNeighborhood {X : UU} (B : X → (X → hProp) → hProp) :=
  (∏ x, isfilter_imply (B x))
    × (∏ x, isfilter_htrue (B x))
    × (∏ x, isfilter_and (B x))
    × (∏ x P, B x P → P x)
    × (∏ x P, B x P → ∃ Q, B x Q × ∏ y, Q y → B y P).

Lemma isNeighborhood_neighborhood {T : TopologicalSet} :
  isNeighborhood (neighborhood (T := T)).
Proof.
  repeat split.
  - intros x A B.
    apply (neighborhood_imply x).
  - intros x.
    apply (pr2 (neighborhood_isOpen _)).
    exact (isOpen_htrue (T := T)).
    apply tt.
  - intros A B.
    apply neighborhood_and.
  - intros x P.
    apply neighborhood_point.
  - intros x P.
    apply neighborhood_neighborhood.
Qed.

Section TopologyFromNeighborhood.

Context {X : UU}.
Context (N : X → (X → hProp) → hProp).
Context (Himpl : ∏ x, isfilter_imply (N x))
        (Htrue : ∏ x, isfilter_htrue (N x))
        (Hand : ∏ x, isfilter_and (N x))
        (Hpt : ∏ x P, N x P → P x)
        (H : ∏ x P, N x P → ∃ Q, N x Q × ∏ y, Q y → N y P).

Definition topologyfromneighborhood (A : X → hProp) :=
  ∏ x : X, A x → N x A.
Lemma isaprop_topologyfromneighborhood :
  ∏ A, isaprop (topologyfromneighborhood A).
Proof.
  intros A.
  apply impred_isaprop ; intros x ;
  apply isapropimpl, propproperty.
Qed.

Lemma topologyfromneighborhood_open :
  isSetOfOpen_union
   (λ A : X → hProp,
          hProppair (topologyfromneighborhood A)
                    (isaprop_topologyfromneighborhood A)).
Proof.
  intros L Hl x.
  apply hinhuniv.
  intros A.
  apply Himpl with (pr1 A).
  intros y Hy.
  apply hinhpr.
  now exists (pr1 A), (pr1 (pr2 A)).
  apply Hl.
  exact (pr1 (pr2 A)).
  exact (pr2 (pr2 A)).
Qed.

End TopologyFromNeighborhood.

Definition TopologyFromNeighborhood {X : UU} (N : X → (X → hProp) → hProp) (H : isNeighborhood N) : TopologicalSet.
Proof.
  simple refine (mkTopologicalSet _ _ _ _ _).
  - apply X.
  - intros A.
    simple refine (hProppair _ _).
    apply (topologyfromneighborhood N A).
    apply isaprop_topologyfromneighborhood.
  - apply topologyfromneighborhood_open.
    apply (pr1 H).
  - intros x _.
    apply (pr1 (pr2 H)).
  - intros A B Ha Hb x Hx.
    apply (pr1 (pr2 (pr2 H))).
    now apply Ha, (pr1 Hx).
    now apply Hb, (pr2 Hx).
Defined.

Lemma TopologyFromNeighborhood_correct {X : UU} (N : X → (X → hProp) → hProp) (H : isNeighborhood N) :
  ∏ (x : X) (P : X → hProp),
    N x P <-> neighborhood (T := TopologyFromNeighborhood N H) x P.
Proof.
  split.
  - intros Hx.
    apply hinhpr.
    simple refine (tpair _ _ _).
    simple refine (tpair _ _ _).
    + intros y.
      apply (N y P).
    + simpl ; intros y Hy.
      generalize (pr2 (pr2 (pr2 (pr2 H))) _ _ Hy).
      apply hinhuniv.
      intros Q.
      apply (pr1 H) with (2 := pr1 (pr2 Q)).
      exact (pr2 (pr2 Q)).
    + split ; simpl.
      exact Hx.
      intros y.
      now apply (pr1 (pr2 (pr2 (pr2 H)))).
  - apply hinhuniv.
    intros O.
    apply (pr1 H) with (pr1 (pr1 O)).
    apply (pr2 (pr2 O)).
    simple refine (pr2 (pr1 O) _ _).
    exact (pr1 (pr2 O)).
Qed.

Lemma isNeighborhood_isPreFilter {X : UU} N :
  isNeighborhood N -> ∏ x : X, isPreFilter (N x).
Proof.
  intros Hn x.
  split.
  - apply (pr1 Hn).
  - apply isfilter_finite_intersection_carac.
    + apply (pr1 (pr2 Hn)).
    + apply (pr1 (pr2 (pr2 Hn))).
Qed.
Lemma isNeighborhood_isFilter {X : UU} N :
  isNeighborhood N -> ∏ x : X, isFilter (N x).
Proof.
  intros Hn x.
  split.
  - apply isNeighborhood_isPreFilter, Hn.
  - intros A Fa.
    apply hinhpr.
    exists x.
    apply ((pr1 (pr2 (pr2 (pr2 Hn)))) _ _ Fa).
Qed.

(** *** Generated Topology *)

Section topologygenerated.

Context {X : UU} (O : (X → hProp) → hProp).

Definition topologygenerated :=
  λ (x : X) (A : X → hProp),
  (∃ L : Sequence (X → hProp), (∏ n, O (L n)) × (finite_intersection L x) × (∏ y, finite_intersection L y → A y)).

Lemma topologygenerated_imply :
  ∏ x : X, isfilter_imply (topologygenerated x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros L.
  exists (pr1 L).
  repeat split.
  exact (pr1 (pr2 L)).
  exact (pr1 (pr2 (pr2 L))).
  intros y Hy.
  apply H, (pr2 (pr2 (pr2 L))), Hy.
Qed.

Lemma topologygenerated_htrue :
  ∏ x : X, isfilter_htrue (topologygenerated x).
Proof.
  intros x.
  apply hinhpr.
  exists nil.
  repeat split; intros n; induction (nopathsfalsetotrue (pr2 n)).
Qed.

Lemma topologygenerated_and :
  ∏ x : X, isfilter_and (topologygenerated x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros La Lb.
  exists (concatenate (pr1 La) (pr1 Lb)).
  repeat split.
  - simpl ; intro.
    apply (coprod_rect (λ x, O (coprod_rect _ _ _ x))) ; intros m.
    + rewrite coprod_rect_compute_1.
      exact (pr1 (pr2 La) _).
    + rewrite coprod_rect_compute_2.
      exact (pr1 (pr2 Lb) _).
  - simpl ; intro.
    apply (coprod_rect (λ y, (coprod_rect (λ _ : stn (length (pr1 La)) ⨿ stn (length (pr1 Lb)), X → hProp) (λ j : stn (length (pr1 La)), (pr1 La) j)
       (λ k : stn (length (pr1 Lb)), (pr1 Lb) k) y) x)) ; intros m.
    + rewrite coprod_rect_compute_1.
      exact (pr1 (pr2 (pr2 La)) _).
    + rewrite coprod_rect_compute_2.
      exact (pr1 (pr2 (pr2 Lb)) _).
  - apply (pr2 (pr2 (pr2 La))).
    intros n.
    simpl in X0.
    unfold concatenate' in X0.
    specialize (X0 (weqfromcoprodofstn_map (length (pr1 La)) (length (pr1 Lb)) (ii1 n))).
    now rewrite (weqfromcoprodofstn_eq1 _ _) , coprod_rect_compute_1 in X0.
  - apply (pr2 (pr2 (pr2 Lb))).
    intros n.
    simpl in X0.
    unfold concatenate' in X0.
    specialize (X0 (weqfromcoprodofstn_map (length (pr1 La)) (length (pr1 Lb)) (ii2 n))).
    now rewrite (weqfromcoprodofstn_eq1 _ _), coprod_rect_compute_2 in X0.
Qed.

Lemma topologygenerated_point :
  ∏ (x : X) (P : X → hProp), topologygenerated x P → P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros L.
  apply (pr2 (pr2 (pr2 L))).
  exact (pr1 (pr2 (pr2 L))).
Qed.

Lemma topologygenerated_neighborhood :
∏ (x : X) (P : X → hProp),
 topologygenerated x P
 → ∃ Q : X → hProp,
    topologygenerated x Q × (∏ y : X, Q y → topologygenerated y P).
Proof.
  intros x P.
  apply hinhfun.
  intros L.
  exists (finite_intersection (pr1 L)).
  split.
  - apply hinhpr.
    exists (pr1 L).
    repeat split.
    exact (pr1 (pr2 L)).
    exact (pr1 (pr2 (pr2 L))).
    easy.
  - intros y Hy.
    apply hinhpr.
    exists (pr1 L).
    repeat split.
    exact (pr1 (pr2 L)).
    exact Hy.
    exact (pr2 (pr2 (pr2 L))).
Qed.

End topologygenerated.

Definition TopologyGenerated {X : UU} (O : (X → hProp) → hProp) : TopologicalSet.
Proof.
  simple refine (TopologyFromNeighborhood _ _).
  - apply X.
  - apply topologygenerated, O.
  - repeat split.
    + apply topologygenerated_imply.
    + apply topologygenerated_htrue.
    + apply topologygenerated_and.
    + apply topologygenerated_point.
    + apply topologygenerated_neighborhood.
Defined.

Lemma TopologyGenerated_included {X : UU} :
  ∏ (O : (X → hProp) → hProp) (P : X → hProp),
    O P → isOpen (T := TopologyGenerated O) P.
Proof.
  intros O P Op.
  apply neighborhood_isOpen.
  intros x Hx.
  apply TopologyFromNeighborhood_correct.
  apply hinhpr.
  exists (singletonSequence P).
  repeat split.
  - induction n as [n Hn].
    exact Op.
  - intros n ;
    induction n as [n Hn].
    exact Hx.
  - intros y Hy.
    now apply (Hy (0%nat,,paths_refl _)).
Qed.
Lemma TopologyGenerated_smallest {X : UU} :
  ∏ (O : (X → hProp) → hProp) (T : isTopologicalSet X),
    (∏ P : X → hProp, O P → pr1 T P)
    → ∏ P : X → hProp, isOpen (T := TopologyGenerated O) P → pr1 T P.
Proof.
  intros O T Ht P Hp.
  apply (neighborhood_isOpen (T := (X,,T))).
  intros x Px.
  generalize (Hp x Px) ; clear Hp.
  apply hinhfun.
  intros L.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (finite_intersection (pr1 L)).
  apply (isOpen_finite_intersection (T := X,,T)).
  intros m.
  apply Ht.
  apply (pr1 (pr2 L)).
  split.
  exact (pr1 (pr2 (pr2 L))).
  exact (pr2 (pr2 (pr2 L))).
Qed.

(** *** Product of topologies *)

Section topologydirprod.

Context (U V : TopologicalSet).

Definition topologydirprod :=
  λ (z : U × V) (A : U × V → hProp),
  (∃ (Ax : U → hProp) (Ay : V → hProp),
      (Ax (pr1 z) × isOpen Ax)
        × (Ay (pr2 z) × isOpen Ay)
        × (∏ x y, Ax x → Ay y → A (x,,y))).

Lemma topologydirprod_imply :
  ∏ x : U × V, isfilter_imply (topologydirprod x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros AB.
  exists (pr1 AB), (pr1 (pr2 AB)) ; split ; [ | split].
  exact (pr1 (pr2 (pr2 AB))).
  exact (pr1 (pr2 (pr2 (pr2 AB)))).
  intros x' y' Hx' Hy'.
  now apply H, (pr2 (pr2 (pr2 (pr2 AB)))).
Qed.

Lemma topologydirprod_htrue :
  ∏ x : U × V, isfilter_htrue (topologydirprod x).
Proof.
  intros z.
  apply hinhpr.
  exists (λ _, htrue), (λ _, htrue).
  repeat split.
  apply isOpen_htrue.
  apply isOpen_htrue.
Qed.

Lemma topologydirprod_and :
  ∏ x : U × V, isfilter_and (topologydirprod x).
Proof.
  intros z A B.
  apply hinhfun2.
  intros A' B'.
  exists (λ x, pr1 A' x ∧ pr1 B' x), (λ y, pr1 (pr2 A') y ∧ pr1 (pr2 B') y).
  repeat split.
  apply (pr1 (pr1 (pr2 (pr2 A')))).
  apply (pr1 (pr1 (pr2 (pr2 B')))).
  apply isOpen_and.
  apply (pr2 (pr1 (pr2 (pr2 A')))).
  apply (pr2 (pr1 (pr2 (pr2 B')))).
  apply (pr1 (pr1 (pr2 (pr2 (pr2 A'))))).
  apply (pr1 (pr1 (pr2 (pr2 (pr2 B'))))).
  apply isOpen_and.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 A'))))).
  apply (pr2 (pr1 (pr2 (pr2 (pr2 B'))))).
  apply (pr2 (pr2 (pr2 (pr2 A')))).
  apply (pr1 X).
  apply (pr1 X0).
  apply (pr2 (pr2 (pr2 (pr2 B')))).
  apply (pr2 X).
  apply (pr2 X0).
Qed.

Lemma topologydirprod_point :
  ∏ (x : U × V) (P : U × V → hProp), topologydirprod x P → P x.
Proof.
  intros xy A.
  apply hinhuniv.
  intros A'.
  rewrite (tppr xy).
  apply (pr2 (pr2 (pr2 (pr2 A')))).
  exact (pr1 (pr1 (pr2 (pr2 A')))).
  exact (pr1 (pr1 (pr2 (pr2 (pr2 A'))))).
Qed.

Lemma topologydirprod_neighborhood :
  ∏ (x : U × V) (P : U × V → hProp),
    topologydirprod x P
    → ∃ Q : U × V → hProp,
      topologydirprod x Q
                      × (∏ y : U × V, Q y → topologydirprod y P).
Proof.
  intros xy P.
  apply hinhfun.
  intros A'.
  exists (λ z, pr1 A' (pr1 z) ∧ pr1 (pr2 A') (pr2 z)).
  split.
  - apply hinhpr.
    exists (pr1 A'), (pr1 (pr2 A')).
    split.
    exact (pr1 (pr2 (pr2 A'))).
    split.
    exact (pr1 (pr2 (pr2 (pr2 A')))).
    intros x' y' Ax' Ay'.
    now split.
  - intros z Az.
    apply hinhpr.
    exists (pr1 A'), (pr1 (pr2 A')).
    repeat split.
    exact (pr1 Az).
    exact (pr2 (pr1 (pr2 (pr2 A')))).
    exact (pr2 Az).
    exact (pr2 (pr1 (pr2 (pr2 (pr2 A'))))).
    exact (pr2 (pr2 (pr2 (pr2 A')))).
Qed.

End topologydirprod.

Definition TopologyDirprod (U V : TopologicalSet) : TopologicalSet.
Proof.
  simple refine (TopologyFromNeighborhood _ _).
  - apply (U × V).
  - apply topologydirprod.
  - repeat split.
    + apply topologydirprod_imply.
    + apply topologydirprod_htrue.
    + apply topologydirprod_and.
    + apply topologydirprod_point.
    + apply topologydirprod_neighborhood.
Defined.

Definition locally2d {T S : TopologicalSet} (x : T) (y : S) : Filter (T × S) :=
  FilterDirprod (locally x) (locally y).

Lemma locally2d_correct {T S : TopologicalSet} (x : T) (y : S) :
  ∏ P : T × S → hProp, locally2d x y P <-> locally (T := TopologyDirprod T S) (x,,y) P.
Proof.
  intros P.
  split ; apply hinhuniv.
  - intros A.
    apply TopologyFromNeighborhood_correct.
    generalize (pr1 (pr2 (pr2 A))) (pr1 (pr2 (pr2 (pr2 A)))).
    apply hinhfun2.
    intros Ox Oy.
    exists (pr1 Ox), (pr1 Oy).
    repeat split.
    + exact (pr1 (pr2 Ox)).
    + exact (pr2 (pr1 Ox)).
    + exact (pr1 (pr2 Oy)).
    + exact (pr2 (pr1 Oy)).
    + intros x' y' Hx' Hy'.
      apply (pr2 (pr2 (pr2 (pr2 A)))).
      now apply (pr2 (pr2 Ox)).
      now apply (pr2 (pr2 Oy)).
  - intros O.
    generalize (pr2 (pr1 O) _ (pr1 (pr2 O))).
    apply hinhfun.
    intros A.
    exists (pr1 A), (pr1 (pr2 A)).
    repeat split.
    apply (pr2 (neighborhood_isOpen _)).
    exact (pr2 (pr1 (pr2 (pr2 A)))).
    exact (pr1 (pr1 (pr2 (pr2 A)))).
    apply (pr2 (neighborhood_isOpen _)).
    exact (pr2 (pr1 (pr2 (pr2 (pr2 A))))).
    exact (pr1 (pr1 (pr2 (pr2 (pr2 A))))).
    intros x' y' Ax' Ay'.
    apply (pr2 (pr2 O)).
    now apply (pr2 (pr2 (pr2 (pr2 A)))).
Qed.

(** *** Topology on a subtype *)

Section topologysubtype.

Context {T : TopologicalSet} (dom : T → hProp).

Definition topologysubtype :=
  λ (x : ∑ x : T, dom x) (A : (∑ x0 : T, dom x0) → hProp),
  ∃ B : T → hProp,
    (B (pr1 x) × isOpen B) × (∏ y : ∑ x0 : T, dom x0, B (pr1 y) → A y).

Lemma topologysubtype_imply :
  ∏ x : ∑ x : T, dom x, isfilter_imply (topologysubtype x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros A'.
  exists (pr1 A').
  split.
  exact (pr1 (pr2 A')).
  intros y Hy.
  now apply H, (pr2 (pr2 A')).
Qed.

Lemma topologysubtype_htrue :
  ∏ x : ∑ x : T, dom x, isfilter_htrue (topologysubtype x).
Proof.
  intros x.
  apply hinhpr.
  exists (λ _, htrue).
  repeat split.
  now apply isOpen_htrue.
Qed.

Lemma topologysubtype_and :
  ∏ x : ∑ x : T, dom x, isfilter_and (topologysubtype x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros A' B'.
  exists (λ x, pr1 A' x ∧ pr1 B' x).
  repeat split.
  exact (pr1 (pr1 (pr2 A'))).
  exact (pr1 (pr1 (pr2 B'))).
  apply isOpen_and.
  exact (pr2 (pr1 (pr2 A'))).
  exact (pr2 (pr1 (pr2 B'))).
  apply (pr2 (pr2 A')), (pr1 X).
  apply (pr2 (pr2 B')), (pr2 X).
Qed.

Lemma topologysubtype_point :
  ∏ (x : ∑ x : T, dom x) (P : (∑ x0 : T, dom x0) → hProp),
    topologysubtype x P → P x.
Proof.
  intros x A.
  apply hinhuniv.
  intros B.
  apply (pr2 (pr2 B)), (pr1 (pr1 (pr2 B))).
Qed.

Lemma topologysubtype_neighborhood :
  ∏ (x : ∑ x : T, dom x) (P : (∑ x0 : T, dom x0) → hProp),
    topologysubtype x P
    → ∃ Q : (∑ x0 : T, dom x0) → hProp,
      topologysubtype x Q
       × (∏ y : ∑ x0 : T, dom x0, Q y → topologysubtype y P).
Proof.
  intros x A.
  apply hinhfun.
  intros B.
  exists (λ y : ∑ x : T, dom x, pr1 B (pr1 y)).
  split.
  - apply hinhpr.
    exists (pr1 B).
    split.
    exact (pr1 (pr2 B)).
    easy.
  - intros y By.
    apply hinhpr.
    exists (pr1 B).
    repeat split.
    exact By.
    exact (pr2 (pr1 (pr2 B))).
    exact (pr2 (pr2 B)).
Qed.

End topologysubtype.

Definition TopologySubtype {T : TopologicalSet} (dom : T → hProp) : TopologicalSet.
Proof.
  simple refine (TopologyFromNeighborhood _ _).
  - exact (∑ x : T, dom x).
  - apply topologysubtype.
  - repeat split.
    + apply topologysubtype_imply.
    + apply topologysubtype_htrue.
    + apply topologysubtype_and.
    + apply topologysubtype_point.
    + apply topologysubtype_neighborhood.
Defined.

(** ** Limits in a Topological Set *)

Section locally_base.

Context {T : TopologicalSet} (x : T) (base : base_of_neighborhood x).

Lemma locally_base_imply :
  isfilter_imply (neighborhood' x base).
Proof.
  intros A B H Ha.
  apply (pr2 (neighborhood_equiv _ _ _)).
  eapply neighborhood_imply.
  exact H.
  eapply neighborhood_equiv.
  exact Ha.
Qed.
Lemma locally_base_htrue :
  isfilter_htrue (neighborhood' x base).
Proof.
  apply (pr2 (neighborhood_equiv _ _ _)).
  apply (pr2 (neighborhood_isOpen _)).
  apply isOpen_htrue.
  apply tt.
Qed.
Lemma locally_base_and :
  isfilter_and (neighborhood' x base).
Proof.
  intros A B Ha Hb.
  apply (pr2 (neighborhood_equiv _ _ _)).
  eapply neighborhood_and.
  eapply neighborhood_equiv, Ha.
  eapply neighborhood_equiv, Hb.
Qed.

End locally_base.

Definition locally_base {T : TopologicalSet} (x : T) (base : base_of_neighborhood x) : Filter T.
Proof.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood' x base).
  - apply locally_base_imply.
  - apply locally_base_htrue.
  - apply locally_base_and.
  - intros A Ha.
    apply neighborhood_equiv in Ha.
    apply neighborhood_point in Ha.
    apply hinhpr.
    now exists x.
Defined.

(** *** Limit of a filter *)

Definition is_filter_lim {T : TopologicalSet} (F : Filter T) (x : T) :=
  filter_le F (locally x).
Definition ex_filter_lim  {T : TopologicalSet} (F : Filter T) :=
  ∃ (x : T), is_filter_lim F x.

Definition is_filter_lim_base {T : TopologicalSet} (F : Filter T) (x : T) base :=
  filter_le F (locally_base x base).
Definition ex_filter_lim_base  {T : TopologicalSet} (F : Filter T) :=
  ∃ (x : T) base, is_filter_lim_base F x base.

Lemma is_filter_lim_base_correct {T : TopologicalSet} (F : Filter T) (x : T) base :
  is_filter_lim_base F x base <-> is_filter_lim F x.
Proof.
  split.
  - intros Hx P HP.
    apply (pr2 (neighborhood_equiv _ base _)) in HP.
    apply Hx.
    exact HP.
  - intros Hx P HP.
    apply neighborhood_equiv in HP.
    apply Hx.
    exact HP.
Qed.
Lemma ex_filter_lim_base_correct {T : TopologicalSet} (F : Filter T) :
  ex_filter_lim_base F <-> ex_filter_lim F.
Proof.
  split.
  - apply hinhfun.
    intros x.
    exists (pr1 x).
    eapply is_filter_lim_base_correct.
    exact (pr2 (pr2 x)).
  - apply hinhfun.
    intros x.
    exists (pr1 x), (base_of_neighborhood_default (pr1 x)).
    apply (pr2 (is_filter_lim_base_correct _ _ _)).
    exact (pr2 x).
Qed.

(** *** Limit of a function *)

Definition is_lim {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) (x : T) :=
  filterlim f F (locally x).
Definition ex_lim {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) :=
  ∃ (x : T), is_lim f F x.

Definition is_lim_base {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) (x : T) base :=
  filterlim f F (locally_base x base).
Definition ex_lim_base {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) :=
  ∃ (x : T) base, is_lim_base f F x base.

Lemma is_lim_base_correct {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) (x : T) base :
  is_lim_base f F x base <-> is_lim f F x.
Proof.
  split.
  - intros Hx P HP.
    apply Hx, (pr2 (neighborhood_equiv _ _ _)).
    exact HP.
  - intros Hx P HP.
    eapply Hx, neighborhood_equiv.
    exact HP.
Qed.
Lemma ex_lim_base_correct {X : UU} {T : TopologicalSet} (f : X → T) (F : Filter X) :
  ex_lim_base f F <-> ex_lim f F.
Proof.
  split.
  - apply hinhfun.
    intros x.
    exists (pr1 x).
    eapply is_lim_base_correct.
    exact (pr2 (pr2 x)).
  - apply hinhfun.
    intros x.
    exists (pr1 x), (base_of_neighborhood_default (pr1 x)).
    apply (pr2 (is_lim_base_correct _ _ _ _)).
    exact (pr2 x).
Qed.

(** *** Continuity *)

Definition continuous_at {U V : TopologicalSet} (f : U → V) (x : U) :=
  is_lim f (locally x) (f x).

Definition continuous_on {U V : TopologicalSet} (dom : U → hProp) (f : ∏ (x : U), dom x → V) :=
  ∏ (x : U) (Hx : dom x),
    ∃ H,
      is_lim (λ y : (∑ x : U, dom x), f (pr1 y) (pr2 y)) (FilterSubtype (locally x) dom H) (f x Hx).
Definition continuous {U V : TopologicalSet} (f : U → V) :=
  ∏ x : U, continuous_at f x.

Lemma isaprop_continuous (x y : TopologicalSet)
  (f : x → y)
  : isaprop (continuous (λ x0 : x,  f x0)).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply propproperty.
Qed.

Definition continuous_base_at {U V : TopologicalSet} (f : U → V) (x : U) base_x base_fx :=
  is_lim_base f (locally_base x base_x) (f x) base_fx.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {U V W : TopologicalSet} (f : U → V → W) (x : U) (y : V) :=
  is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (FilterDirprod (locally x) (locally y)) (f x y).
Definition continuous2d {U V W : TopologicalSet} (f : U → V → W) :=
  ∏ (x : U) (y : V), continuous2d_at f x y.

Definition continuous2d_base_at {U V W : TopologicalSet} (f : U → V → W)
           (x : U) (y : V) base_x base_y base_fxy :=
  is_lim_base (λ z : U × V, f (pr1 z) (pr2 z))
              (FilterDirprod (locally_base x base_x) (locally_base y base_y))
              (f x y) base_fxy.

(** *** Continuity of basic functions *)

Lemma continuous_comp {X : UU} {U V : TopologicalSet} (f : X → U) (g : U → V) (F : Filter X) (l : U) :
  is_lim f F l → continuous_at g l →
  is_lim (funcomp f g) F (g l).
Proof.
  apply filterlim_comp.
Qed.

Lemma continuous_funcomp {X Y Z : TopologicalSet} (f : X → Y) (g : Y → Z) :
  continuous f → continuous g →
  continuous (funcomp f g).
Proof.
  intros Hf Hg x.
  refine (continuous_comp _ _ _ _ _ _).
  apply Hf.
  apply Hg.
Qed.


Lemma continuous2d_comp {X : UU} {U V W : TopologicalSet} (f : X → U) (g : X → V) (h : U → V → W) (F : Filter X) (lf : U) (lg : V) :
  is_lim f F lf → is_lim g F lg → continuous2d_at h lf lg →
  is_lim (λ x, h (f x) (g x)) F (h lf lg).
Proof.
  intros Hf Hg.
  apply (filterlim_comp (λ x, (f x ,, g x))).
  intros P.
  apply hinhuniv.
  intros Hp.
  generalize (filter_and F _ _ (Hf _ (pr1 (pr2 (pr2 Hp)))) (Hg _ (pr1 (pr2 (pr2 (pr2 Hp)))))).
  apply (filter_imply F).
  intros x Hx.
  apply (pr2 (pr2 (pr2 (pr2 Hp)))).
  exact (pr1 Hx).
  exact (pr2 Hx).
Qed.

Lemma continuous_tpair {U V : TopologicalSet} :
  continuous2d (W := TopologyDirprod U V) (λ (x : U) (y : V), (x,,y)).
Proof.
  intros x y P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 O).
  - exact (pr2 (pr2 O)).
  - generalize (pr2 (pr1 O) _ (pr1 (pr2 O))).
    apply hinhfun.
    intros Ho.
    exists (pr1 Ho), (pr1 (pr2 Ho)).
    repeat split.
    + apply (pr2 (neighborhood_isOpen _)).
      exact (pr2 (pr1 (pr2 (pr2 Ho)))).
      exact (pr1 (pr1 (pr2 (pr2 Ho)))).
    + apply (pr2 (neighborhood_isOpen _)).
      exact (pr2 (pr1 (pr2 (pr2 (pr2 Ho))))).
      exact (pr1 (pr1 (pr2 (pr2 (pr2 Ho))))).
    + exact (pr2 (pr2 (pr2 (pr2 Ho)))).
Qed.
Lemma continuous_pr1 {U V : TopologicalSet} :
  continuous (U := TopologyDirprod U V) (λ (xy : U × V), pr1 xy).
Proof.
  intros xy P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 (pr1 O)).
  - exact (pr2 (pr2 O)).
  - apply hinhpr.
    mkpair.
    mkpair.
    + apply (λ xy : U × V, pr1 O (pr1 xy)).
    + intros xy' Oxy.
      apply hinhpr.
      exists (pr1 O), (λ _, htrue).
      repeat split.
      exact Oxy.
      exact (pr2 (pr1 O)).
      exact isOpen_htrue.
      easy.
    + repeat split.
      * exact (pr1 (pr2 O)).
      * easy.
Qed.
Lemma continuous_pr2 {U V : TopologicalSet} :
  continuous (U := TopologyDirprod U V) (λ (xy : U × V), pr2 xy).
Proof.
  intros xy P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 (pr1 O)).
  - exact (pr2 (pr2 O)).
  - apply hinhpr.
    mkpair.
    mkpair.
    + apply (λ xy : U × V, pr1 O (pr2 xy)).
    + intros xy' Oxy.
      apply hinhpr.
      exists (λ _, htrue), (pr1 O).
      repeat split.
      exact isOpen_htrue.
      exact Oxy.
      exact (pr2 (pr1 O)).
      easy.
    + repeat split.
      * exact (pr1 (pr2 O)).
      * easy.
Qed.

(** ** Topology in algebraic structures *)

Definition isTopological_monoid (X : monoid) (is : isTopologicalSet X) :=
  continuous2d (U := ((pr1 (pr1 (pr1 X))) ,, is))
               (V := ((pr1 (pr1 (pr1 X))) ,, is))
               (W := ((pr1 (pr1 (pr1 X))) ,, is)) BinaryOperations.op.
Definition Topological_monoid :=
  ∑ (X : monoid) (is : isTopologicalSet X), isTopological_monoid X is.

Definition isTopological_gr (X : gr) (is : isTopologicalSet X) :=
  isTopological_monoid X is
  × continuous (U := ((pr1 (pr1 (pr1 X))) ,, is)) (V := ((pr1 (pr1 (pr1 X))) ,, is)) (grinv X).
Definition Topological_gr :=
  ∑ (X : gr) is, isTopological_gr X is.

Definition isTopological_rig (X : rig) (is : isTopologicalSet X) :=
  isTopological_monoid (rigaddabmonoid X) is
  × isTopological_monoid (rigmultmonoid X) is.
Definition Topological_rig :=
  ∑ (X : rig) is, isTopological_rig X is.

Definition isTopological_rng (X : rng) (is : isTopologicalSet X) :=
  isTopological_gr (rngaddabgr X) is
  × isTopological_monoid (rigmultmonoid X) is.
Definition Topological_rng :=
  ∑ (X : rng) is, isTopological_rng X is.

Definition isTopological_DivRig (X : DivRig) (is : isTopologicalSet X) :=
  isTopological_rig (pr1 X) is
  × continuous_on (U := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (V := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (λ x : X, hProppair (x != 0%dr) (isapropneg _)) (λ x Hx, invDivRig (x,,Hx)).
Definition Topological_DivRig :=
  ∑ (X : DivRig) is, isTopological_DivRig X is.

Definition isTopological_fld (X : fld) (is : isTopologicalSet X) :=
  isTopological_rng (pr1 X) is
  × continuous_on (U := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (V := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (λ x : X, hProppair (x != 0%rng) (isapropneg _))
                  fldmultinv.
Definition Topological_fld :=
  ∑ (X : fld) is, isTopological_fld X is.

Definition isTopological_ConstructiveDivisionRig (X : ConstructiveDivisionRig) (is : isTopologicalSet X) :=
  isTopological_rig (pr1 X) is
  × continuous_on (U := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                        (V := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                        (λ x : X, (x ≠ 0)%CDR) CDRinv.
Definition Topological_ConstructiveDivisionRig :=
  ∑ (X : ConstructiveDivisionRig) is, isTopological_ConstructiveDivisionRig X is.

Definition isTopological_ConstructiveField (X : ConstructiveField) (is : isTopologicalSet X) :=
  isTopological_rng (pr1 X) is
  × continuous_on (U := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (V := ((pr1 (pr1 (pr1 (pr1 X)))) ,, is))
                  (λ x : X, (x ≠ 0)%CF) CFinv.
Definition Topological_ConstructiveField :=
  ∑ (X : ConstructiveField) is, isTopological_ConstructiveField X is.
