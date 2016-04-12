(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Filters.
Require Import UniMath.Foundations.Algebra.DivisionRig.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.

Section OpenSet.

Context {X : UU}.
Context (isOpen : (X -> hProp) -> hProp).

Definition isOpenSet_infinite_union : hProp :=
  hProppair
    (∀ P : (X -> hProp) -> hProp,
       (∀ A : X -> hProp, P A -> isOpen A) -> isOpen (infinite_union P))
    (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Definition isOpenSet_finite_intersection : hProp :=
  hProppair
    (∀ (P : Sequence (X -> hProp)), (∀ m, isOpen (P m)) -> isOpen (finite_intersection P))
    (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).

Lemma isOpenSet_hfalse :
  isOpenSet_infinite_union
  -> isOpen (λ _ : X, hfalse).
Proof.
  intros H0.
  rewrite <- infinite_union_hfalse.
  apply H0.
  intro.
  apply fromempty.
Qed.

Lemma isOpenSet_finite_intersection_htrue :
  isOpenSet_finite_intersection
  -> isOpen (λ _, htrue).
Proof.
  intro H0.
  rewrite <- finite_intersection_htrue.
  apply H0.
  intros (m,Hm).
  now apply fromempty.
Qed.
Lemma isOpenSet_finite_intersection_and :
  isOpenSet_finite_intersection
  -> ∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x).
Proof.
  intros H0 A B Ha Hb.
  rewrite <- finite_intersection_and.
  apply H0.
  intros (m,Hm) ; simpl.
  destruct m.
  apply Ha.
  apply Hb.
Qed.
Lemma isOpenSet_finite_intersection_carac :
  isOpen (λ _, htrue)
  -> (∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x))
  -> isOpenSet_finite_intersection.
Proof.
  intros Htrue Hpair L.
  apply (pr2 (finite_intersection_hProp isOpen)).
  split.
  - exact Htrue.
  - exact Hpair.
Qed.

Definition isOpenSet :=
  isOpenSet_infinite_union ∧ isOpenSet_finite_intersection.

End OpenSet.

Definition isTopologicalSet :=
  λ X : hSet, Σ isOpen : (X -> hProp) -> hProp, isOpenSet isOpen.
Definition TopologicalSet := Σ X : hSet, isTopologicalSet X.

Definition mkTopologicalSet (X : hSet) (isOpen : (X -> hProp) -> hProp) (is : isOpenSet_infinite_union isOpen) (is0 : isOpen (λ _, htrue)) (is1 : ∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x)) : TopologicalSet := (X,,isOpen,,is,,(isOpenSet_finite_intersection_carac _ is0 is1)).

Definition pr1TopologicatSet : TopologicalSet -> hSet := pr1.
Coercion pr1TopologicatSet : TopologicalSet >-> hSet.

Definition isOpen {T : TopologicalSet} : (T -> hProp) -> hProp := pr1 (pr2 T).
Definition Open {T : TopologicalSet} :=
  Σ O : T -> hProp, isOpen O.
Definition pr1Open {T : TopologicalSet} : Open -> (T -> hProp) := pr1.
Coercion pr1Open : Open >-> Funclass.

Section Topology_pty.

Context {T : TopologicalSet}.

Lemma isOpen_infinite_union :
  ∀ P : (T -> hProp) -> hProp,
    (∀ A : T -> hProp, P A -> isOpen A)
    -> isOpen (infinite_union P).
Proof.
  apply (pr1 (pr2 (pr2 T))).
Qed.
Lemma isOpen_finite_intersection :
  ∀ (P : Sequence (T -> hProp)),
    (∀ m , isOpen (P m))
    -> isOpen (finite_intersection P).
Proof.
  apply (pr2 (pr2 (pr2 T))).
Qed.

Lemma isOpen_hfalse :
  isOpen (λ _ : T, hfalse).
Proof.
  rewrite <- infinite_union_hfalse.
  apply isOpen_infinite_union.
  intro.
  apply fromempty.
Qed.
Lemma isOpen_htrue :
  isOpen (λ _ : T, htrue).
Proof.
  rewrite <- finite_intersection_htrue.
  apply isOpen_finite_intersection.
  intros (m,Hm).
  now apply fromempty.
Qed.
Lemma isOpen_and :
  ∀ A B : T -> hProp,
    isOpen A -> isOpen B -> isOpen (λ x : T, A x ∧ B x).
Proof.
  apply isOpenSet_finite_intersection_and.
  intros P Hp.
  apply isOpen_finite_intersection.
  apply Hp.
Qed.
Lemma isOpen_or :
  ∀ A B : T -> hProp,
    isOpen A -> isOpen B -> isOpen (λ x : T, A x ∨ B x).
Proof.
  intros A B Ha Hb.
  rewrite <- infinite_union_or.
  apply isOpen_infinite_union.
  intros C.
  apply hinhuniv.
  intros [-> | ->].
  exact Ha.
  exact Hb.
Qed.

End Topology_pty.

(** ** Neighborhood *)

Section Neighborhood.

Context {T : TopologicalSet}.

Definition neighborhood (x : T) : (T -> hProp) -> hProp :=
  λ P : T -> hProp, ∃ O : Open, O x × (∀ y : T, O y -> P y).

Lemma neighborhood_isOpen (P : T -> hProp) :
  (∀ x, P x -> neighborhood x P) <-> isOpen P.
Proof.
  split.
  - intros Hp.
    assert (H : ∀ A : T -> hProp, isaprop (∀ y : T, A y -> P y)).
    { intros A.
      apply impred_isaprop.
      intro y.
      apply isapropimpl.
      apply propproperty. }
    set (Q := λ A : T -> hProp, isOpen A ∧ (hProppair (∀ y : T, A y -> P y) (H A))).
    assert (P = (infinite_union Q)).
    { apply funextfun.
      intros x.
      apply uahp.
      - intros Px.
        generalize (Hp _ Px).
        apply hinhfun.
        intros (A,(Ax,Ha)).
        exists A ; split.
        split.
        apply (pr2 A).
        exact Ha.
        exact Ax.
      - apply hinhuniv.
        intros (A,((Ha,Hx),Ax)).
        apply Hx.
        exact Ax. }
    rewrite X.
    apply isOpen_infinite_union.
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

Lemma neighborhood_impl :
  ∀ (x : T) (P Q : T -> hProp),
    (∀ y : T, P y -> Q y) -> neighborhood x P -> neighborhood x Q.
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
  ∀ (x : T) (P : T -> hProp),
    (∀ y, P y) -> neighborhood x P.
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
  ∀ (x : T) (A B : T -> hProp),
    neighborhood x A -> neighborhood x B -> neighborhood x (λ y, A y ∧ B y).
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
  ∀ (x : T) (P : T -> hProp),
    neighborhood x P -> P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros O.
  apply (pr2 (pr2 O)).
  apply (pr1 (pr2 O)).
Qed.

Lemma neighborhood_neighborhood :
  ∀ (x : T) (P : T -> hProp),
    neighborhood x P
    -> ∃ Q : T -> hProp, neighborhood x Q
                        × ∀ y : T, Q y -> neighborhood y P.
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

(** ** Base of Neighborhood *)

Definition is_base_of_neighborhood {T : TopologicalSet} (x : T) (B : (T -> hProp) -> hProp) :=
  (∀ P : T -> hProp, B P -> neighborhood x P)
    × (∀ P : T -> hProp, neighborhood x P -> ∃ Q : T -> hProp, B Q × (∀ t : T, Q t -> P t)).

Definition base_of_neighborhood {T : TopologicalSet} (x : T) :=
  Σ (B : (T -> hProp) -> hProp), is_base_of_neighborhood x B.
Definition pr1base_of_neighborhood {T : TopologicalSet} (x : T) :
  base_of_neighborhood x -> ((T -> hProp) -> hProp) := pr1.
Coercion pr1base_of_neighborhood : base_of_neighborhood >-> Funclass.

Definition base_of_neighborhood_default {T : TopologicalSet} (x : T) : base_of_neighborhood x.
Proof.
  intros T x.
  simple refine (tpair _ _ _).
  intros P.
  apply (P x ∧ isOpen P).
  split.
  - intros P (Px,Hp).
    apply hinhpr.
    now exists (P,,Hp).
  - intros P.
    apply hinhfun.
    intros ((Q,Hq),(Qx,H)).
    exists Q.
    repeat split.
    exact Qx.
    exact Hq.
    exact H.
Defined.

Definition neighborhood' {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) : (T -> hProp) -> hProp :=
  λ P : T -> hProp, ∃ O : T -> hProp, B O × (∀ t : T, O t -> P t).

Lemma neighborhood_equiv {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) :
  ∀ P, neighborhood' x B P <-> neighborhood x P.
Proof.
  intros T x B P.
  split.
  - apply hinhuniv.
    intros O.
    generalize ((pr1 (pr2 B)) (pr1 O) (pr1 (pr2 O))).
    apply neighborhood_impl.
    exact (pr2 (pr2 O)).
  - intros Hp.
    generalize (pr2 (pr2 B) P Hp).
    apply hinhfun.
    intros O.
    exists (pr1 O).
    exact (pr2 O).
Qed.

(** ** Some topologies *)

(** *** Generated Topology *)

Definition generated_topology {X : hSet} (O : (X -> hProp) -> hProp) : TopologicalSet.
Proof.
  intros X O.
  simple refine (mkTopologicalSet _ _ _ _ _).
  - apply X.
  - intros P.
    simple refine (tpair _ _ _).
    apply (∀ x, P x -> ∃ L : Sequence (X -> hProp), (forall n, O (L n) × L n x) × (∀ y : X, (finite_intersection L) y -> P y)).
    apply impred_isaprop ; intro x.
    apply isapropimpl.
    apply propproperty.
  - intros P Hp x.
    apply hinhuniv.
    intros (A,(Pa,Ax)).
    specialize (Hp A Pa x Ax) ; revert Hp.
    apply hinhfun.
    intros (L,(Ol,Hl)).
    exists L.
    split.
    exact Ol.
    intros y Hy.
    apply hinhpr.
    exists A.
    split.
    exact Pa.
    now apply Hl.
  - intros x _.
    apply hinhpr.
    exists nil.
    split.
    now intros (n,Hn).
    intros _ _.
    exact tt.
  - intros A B Ha Hb x (Ax,Bx).
    specialize (Ha _ Ax).
    specialize (Hb _ Bx).
    revert Ha Hb.
    apply hinhfun2.
    intros (La,(Ola,Hla)) (Lb,(Olb,Hlb)).
    exists (concatenate La Lb).
    split.
    + intros n ; simpl.
      destruct (invmap (weqfromcoprodofstn (length La) (length Lb)) n) ; simpl.
      now apply Ola.
      now apply Olb.
    + intros y Hy.
      split.
      apply Hla.
      intros n.
      simpl in Hy.
      specialize (Hy ((weqfromcoprodofstn (length La) (length Lb)) (ii1 n))).
      now rewrite homotinvweqweq, coprod_rect_compute_1 in Hy.
      apply Hlb.
      intros n.
      simpl in Hy.
      specialize (Hy ((weqfromcoprodofstn (length La) (length Lb)) (ii2 n))).
      now rewrite homotinvweqweq, coprod_rect_compute_2 in Hy.
Defined.

Lemma generated_topology_included {X : hSet} :
  ∀ (O : (X -> hProp) -> hProp) (P : X -> hProp),
    O P -> isOpen (T := generated_topology O) P.
Proof.
  intros X O P Op.
  intros x Hx.
  apply hinhpr.
  exists (singletonSequence P).
  split.
  - now simpl.
  - intros y Hy.
    apply (Hy (0%nat,,paths_refl _)).
Qed.
Lemma generated_topology_smallest {X : hSet} :
  ∀ (O : (X -> hProp) -> hProp) (T : isTopologicalSet X),
    (∀ P : X -> hProp, O P -> pr1 T P)
    -> ∀ P : X -> hProp, isOpen (T := generated_topology O) P -> pr1 T P.
Proof.
  intros X O T Ht P Hp.
  apply (neighborhood_isOpen (T := (X,,T))).
  intros x Px.
  generalize (Hp x Px) ; clear Hp.
  apply hinhfun.
  intros (L,(Hl,Hp)).
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (finite_intersection L).
  apply (isOpen_finite_intersection (T := X,,T)).
  intros m.
  apply Ht.
  apply Hl.
  split.
  intros m.
  apply (pr2 (Hl m)).
  apply Hp.
Qed.

(** *** Product of topologies *)

Definition topology_prod (U V : TopologicalSet) : TopologicalSet.
Proof.
  intros U V.
  simple refine (generated_topology _).
  - exists (U × V).
    apply isaset_dirprod ; apply pr2.
  - simpl ; intros A.
    exists ((∀ y : V, isOpen (λ x : U, A (x,,y))) × (∀ x : U, isOpen (λ y : V, A (x,,y)))).
    apply isapropdirprod ; apply impred_isaprop ; intro ; apply pr2.
Defined.

(** *** Topology on a subtype *)

Definition topology_subtypes (T : TopologicalSet) (dom : T -> hProp) : TopologicalSet.
Proof.
  intros T dom.
  simple refine (mkTopologicalSet _ _ _ _ _).
  - exists (Σ x : T, dom x).
    apply isaset_total2.
    apply pr2.
    intros x.
    apply isasetaprop.
    apply pr2.
  - simpl ; intros A.
    apply (∃ A' : Open (T := T), A = (λ (y : Σ x0 : T, dom x0), A' (pr1 y))).
  - intros P Hp.
    simpl in P.
    set (P' := λ A : T -> hProp, isOpen A ∧ P (λ y : (Σ x : T, dom x), A (pr1 y))).
    apply hinhpr.
    simple refine (tpair _ _ _).
    exists (infinite_union P').
    apply isOpen_infinite_union.
    intros A Ha.
    apply (pr1 Ha).
    apply funextfun ; intros (x,Hx).
    apply uahp.
    + apply hinhuniv.
      intros (A,(Ha,Ax)).
      generalize (Hp _ Ha).
      apply hinhfun.
      intros (A',Ha').
      exists A' ; split.
      split.
      apply (pr2 A').
      now rewrite <- Ha'.
      now rewrite Ha' in Ax.
    + apply hinhfun.
      intros (A,(P'a,Ax)).
      exists (λ x, A (pr1 x)).
      split.
      apply (pr2 P'a).
      exact Ax.
  - simpl.
    apply hinhpr.
    now exists ((λ _, htrue),,isOpen_htrue).
  - intros A B.
    apply hinhfun2.
    intros (A',->) (B',->).
    simple refine (tpair _ _ _).
    simple refine (tpair _ _ _).
    intros x ; apply (A' x ∧ B' x).
    apply isOpen_and.
    apply (pr2 A').
    apply (pr2 B').
    reflexivity.
Defined.

(** ** Limits in a Topological Set *)

Definition locally {T : TopologicalSet} (x : T) : Filter T.
Proof.
  intros T x.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood x).
  - intros A B.
    apply neighborhood_impl.
  - apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_htrue.
    apply tt.
  - intros A B.
    apply neighborhood_and.
  - intros Hx.
    apply neighborhood_point in Hx.
    exact Hx.
Defined.

Definition locally_base {T : TopologicalSet} (x : T) (base : base_of_neighborhood x) : Filter T.
Proof.
  intros T x base.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood' x base).
  - intros A B H Ha.
    apply (pr2 (neighborhood_equiv _ _ _)).
    eapply neighborhood_impl.
    exact H.
    eapply neighborhood_equiv.
    exact Ha.
  - apply (pr2 (neighborhood_equiv _ _ _)).
    apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_htrue.
    apply tt.
  - intros A B Ha Hb.
    apply (pr2 (neighborhood_equiv _ _ _)).
    eapply neighborhood_and.
    eapply neighborhood_equiv, Ha.
    eapply neighborhood_equiv, Hb.
  - intros Hx.
    apply neighborhood_equiv in Hx.
    apply neighborhood_point in Hx.
    exact Hx.
Defined.

(** *** Limit of a filter *)

Definition is_filter_lim {T : TopologicalSet} (F : Filter T) (x : T) :=
  filter_le (locally x) F.
Definition ex_filter_lim  {T : TopologicalSet} (F : Filter T) :=
  ∃ (x : T), is_filter_lim F x.

Definition is_filter_lim_base {T : TopologicalSet} (F : Filter T) (x : T) base :=
  filter_le (locally_base x base) F.
Definition ex_filter_lim_base  {T : TopologicalSet} (F : Filter T) :=
  ∃ (x : T) base, is_filter_lim_base F x base.

Lemma is_filter_lim_base_correct {T : TopologicalSet} (F : Filter T) (x : T) base :
  is_filter_lim_base F x base <-> is_filter_lim F x.
Proof.
  intros.
  split.
  - intros Hx P HP.
    eapply neighborhood_equiv, Hx.
    exact HP.
  - intros Hx P HP.
    apply (pr2 (neighborhood_equiv _ _ _)), Hx.
    exact HP.
Qed.
Lemma ex_filter_lim_base_correct {T : TopologicalSet} (F : Filter T) :
  ex_filter_lim_base F <-> ex_filter_lim F.
Proof.
  intros.
  split.
  - apply hinhfun.
    intros (x,(base,Hx)).
    exists x.
    eapply is_filter_lim_base_correct.
    exact Hx.
  - apply hinhfun.
    intros (x,Hx).
    exists x, (base_of_neighborhood_default x).
    now apply (pr2 (is_filter_lim_base_correct _ _ _)).
Qed.

(** *** Limit of a function *)

Definition is_lim {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) (x : T) :=
  filterlim f F (locally x).
Definition ex_lim {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) :=
  ∃ (x : T), is_lim f F x.

Definition is_lim_base {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) (x : T) base :=
  filterlim f F (locally_base x base).
Definition ex_lim_base {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) :=
  ∃ (x : T) base, is_lim_base f F x base.

Lemma is_lim_base_correct {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) (x : T) base :
  is_lim_base f F x base <-> is_lim f F x.
Proof.
  intros.
  split.
  - intros Hx P HP.
    apply Hx, (pr2 (neighborhood_equiv _ _ _)).
    exact HP.
  - intros Hx P HP.
    eapply Hx, neighborhood_equiv.
    exact HP.
Qed.
Lemma ex_lim_base_correct {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter X) :
  ex_lim_base f F <-> ex_lim f F.
Proof.
  intros.
  split.
  - apply hinhfun.
    intros (x,(base,Hx)).
    exists x.
    eapply is_lim_base_correct.
    exact Hx.
  - apply hinhfun.
    intros (x,Hx).
    exists x, (base_of_neighborhood_default x).
    now apply (pr2 (is_lim_base_correct _ _ _ _)).
Qed.

(** *** Continuity *)

Definition continuous_at {U V : TopologicalSet} (f : U -> V) (x : U) :=
  is_lim f (locally x) (f x).

Definition continuous_on {U V : TopologicalSet} (dom : U -> hProp) (f : U -> V) :=
  ∀ (x : U) (Hx : dom x) H,
    is_lim f (filter_dom (locally x) dom H) (f x).
Definition continuous_subtypes {U V : TopologicalSet} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  ∀ (x : Σ x : U, dom x) H,
    is_lim f (filter_subtypes (locally (pr1 x)) dom H) (f x).
Definition continuous {U V : TopologicalSet} (f : U -> V) :=
  ∀ x : U, continuous_at f x.

Definition continuous_base_at {U V : TopologicalSet} (f : U -> V) (x : U) base_x base_fx :=
  is_lim_base f (locally_base x base_x) (f x) base_fx.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {U V W : TopologicalSet} (f : U -> V -> W) (x : U) (y : V) :=
  is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (filter_prod (locally x) (locally y)) (f x y).
Definition continuous2d {U V W : TopologicalSet} (f : U -> V -> W) :=
  ∀ (x : U) (y : V), continuous2d_at f x y.

Definition continuous2d_base_at {U V W : TopologicalSet} (f : U -> V -> W) (x : U) (y : V) base_x base_y base_fxy :=
  is_lim_base (λ z : U × V, f (pr1 z) (pr2 z)) (filter_prod (locally_base x base_x) (locally_base y base_y)) (f x y) base_fxy.

(** ** Topology in algebraic structures *)

Definition isTopological_monoid (X : monoid) (is : isTopologicalSet X) :=
  continuous2d (U := ((pr1 (pr1 X)) ,, is)) (V := ((pr1 (pr1 X)) ,, is)) (W := ((pr1 (pr1 X)) ,, is)) BinaryOperations.op.
Definition Topological_monoid :=
  Σ (X : monoid) (is : isTopologicalSet X), isTopological_monoid X is.

Definition isTopological_gr (X : gr) (is : isTopologicalSet X) :=
  isTopological_monoid X is
  × continuous (U := ((pr1 (pr1 X)) ,, is)) (V := ((pr1 (pr1 X)) ,, is)) (grinv X).
Definition Topological_gr :=
  Σ (X : gr) is, isTopological_gr X is.

Definition isTopological_rig (X : rig) (is : isTopologicalSet X) :=
  isTopological_monoid (rigaddabmonoid X) is
  × isTopological_monoid (rigmultmonoid X) is.
Definition Topological_rig :=
  Σ (X : rig) is, isTopological_rig X is.

Definition isTopological_rng (X : rng) (is : isTopologicalSet X) :=
  isTopological_gr (rngaddabgr X) is
  × isTopological_monoid (rigmultmonoid X) is.
Definition Topological_rng :=
  Σ (X : rng) is, isTopological_rng X is.

Definition isTopological_DivRig (X : DivRig) (is : isTopologicalSet X) :=
  isTopological_rig (pr1 X) is
  × continuous_subtypes (U := ((pr1 (pr1 (pr1 X))) ,, is)) (V := ((pr1 (pr1 (pr1 X))) ,, is)) (λ x : X, hProppair (x != 0%dr) (isapropneg _)) invDivRig.
Definition Topological_DivRig :=
  Σ (X : DivRig) is, isTopological_DivRig X is.

Definition isTopological_fld (X : fld) (is : isTopologicalSet X) :=
  isTopological_rng (pr1 X) is
  × continuous_subtypes (U := ((pr1 (pr1 (pr1 X))) ,, is)) (V := ((pr1 (pr1 (pr1 X))) ,, is)) (λ x : X, hProppair (x != 0%rng) (isapropneg _)) (λ x, fldmultinv (pr1 x) (pr2 x)).
Definition Topological_fld :=
  Σ (X : fld) is, isTopological_fld X is.

Definition isTopological_ConstructiveDivisionRig (X : ConstructiveDivisionRig) (is : isTopologicalSet X) :=
  isTopological_rig (pr1 X) is
  × continuous_subtypes (U := ((pr1 (pr1 (pr1 X))) ,, is)) (V := ((pr1 (pr1 (pr1 X))) ,, is)) (λ x : X, (x ≠ 0)%CDR) (λ x, CDRinv (pr1 x) (pr2 x)).
Definition Topological_ConstructiveDivisionRig :=
  Σ (X : ConstructiveDivisionRig) is, isTopological_ConstructiveDivisionRig X is.

Definition isTopological_ConstructiveField (X : ConstructiveField) (is : isTopologicalSet X) :=
  isTopological_rng (pr1 X) is
  × continuous_subtypes (U := ((pr1 (pr1 (pr1 X))) ,, is)) (V := ((pr1 (pr1 (pr1 X))) ,, is)) (λ x : X, (x ≠ 0)%CF) (λ x, CFinv (pr1 x) (pr2 x)).
Definition Topological_ConstructiveField :=
  Σ (X : ConstructiveField) is, isTopological_ConstructiveField X is.
