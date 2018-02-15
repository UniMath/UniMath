(**** ZF Structures

    Dimitris Tsementzis (@dimtsem), Feb. 2018

Main contents of this file:

         - A definition of "ZF structures" as well-founded rooted trees with no automorphisms plus
           some extra properties [ZFS]
         - A proof that the type [ZFS] of ZF structures is an h-set [isaset_ZFS]
         - A definition of the elementhood relation for ZF structures [ZFS_elementof]

Table of Contents:
      (1) Auxilliary Lemmas
      (2) Basic Definitions
      (3) Definition of ZFS
      (4) The Elementhood Relation

A textbook reference for some of the material in this file can be found in:
         - Mac Lane and Moerdijk, "Sheaves in Geometry and Logic", VI.10

****)

Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.Propositions.
Require Export UniMath.Foundations.Sets.
Require Export UniMath.Foundations.HLevels.

Require Export UniMath.Combinatorics.WellOrderedSets.
Require Export UniMath.Combinatorics.OrderedSets.
Require Export UniMath.MoreFoundations.DecidablePropositions.



(*** Auxilliary Lemmas ***)

(** Contents **)
(**
-Some auxilliary lemmas which which are useful stated in this form for this file.
**)


Lemma iscontr_propid (P : UU) (is : isaprop P) : iscontr (P = P).
Proof.
  assert (π : isaprop (P=P)).
  apply (isofhlevelpathspace 1 P P is is).
  apply (iscontraprop1 π (idpath P)).
Qed.

Lemma contr_to_pr1contr (X : UU) (P : X → hProp) (T : ∑ x, P x) (C : iscontr (T = T)) : iscontr ((pr1 T) = (pr1 T)).
Proof.
  exact (@isofhlevelweqf 0 (T = T) (pr1 T = pr1 T) (@total2_paths_hProp_equiv _ _ T T) C).
Qed.

Lemma pr1contr_to_contr (X : UU) (P : X → hProp) (T : ∑ x, P x) (C : iscontr (pr1 T = pr1 T)) : iscontr (T = T).
Proof.
  exact (@isofhlevelweqb 0 (T = T) (pr1 T = pr1 T) (@total2_paths_hProp_equiv _ _ T T) C).
Qed.

Lemma substructure_univalence (S : UU) (iso : S → S → UU) (u : ∏ (X Y : S), (X = Y) ≃ (iso X Y)) (Q : S → hProp) (A B : (∑ (X : S), Q X)) : (A = B) ≃ (iso (pr1 A) (pr1 B)).
Proof.
  intermediate_weq (pr1 A = pr1 B).
  apply (total2_paths_hProp_equiv Q A B).
  apply (u (pr1 A) (pr1 B)).
Qed.


(*** End of Auxilliary Lemmas ***)


(*** Basic Definitions ***)

(** Contents **)
(**
-Transitive reflexive rooted graph [TRRGraph]
-Tree [Tree]
-Up and Down Well-founded tree [Tree_isWellFounded]
-Rigid tree (no non-trivial automorphisms) [isrigid]
-ZF structures as rigid well-founded trees [ZFStructures]
-Proof that ZFStructures is an h-set [isaset_ZFStruc]
**)

(** The definition of transitive reflexive rooted graphs [TRRGraph] **)

Definition RootedGraph := ∑ (V : hSet) (E : hrel V), V.

Definition isaroot {V : hSet} (E : hrel V) (r : V) : UU := (∏ w : V, E r w).

Lemma isaprop_isaroot {V : hSet} (E : hrel V) (r : V) : isaprop (isaroot E r).
Proof.
  repeat (apply impred ; intros). apply propproperty.
Qed.

Definition isTRR (V : hSet) (E : hrel V) (r : V) : UU :=
  isrefl E × istrans E × isaroot E r.

Lemma isaprop_isTRR (V : hSet) (E : hrel V) (r : V) : isaprop (isTRR V E r).
Proof.
  apply isapropdirprod.
  - apply (isaprop_isrefl E).
  - apply isapropdirprod.
    -- apply (isaprop_istrans E).
    -- apply (isaprop_isaroot E r).
Qed.

Definition TRRGraphData (V : hSet) : UU := ∑ (E : hrel V) (r : V), isTRR V E r.

Lemma isaset_TRRGraphData (V : hSet) : isaset (TRRGraphData V).
Proof.
  unfold TRRGraphData.
  apply (isofhleveltotal2 2).
  - apply isaset_hrel.
  -  intros x.
     apply (isofhleveltotal2 2).
     -- apply setproperty.
     -- intros.  apply hlevelntosn. apply isaprop_isTRR.
Qed.

Definition TRRGraph : UU := ∑ (V : hSet), TRRGraphData V.

Definition TRRG_edgerel (G : TRRGraph) : hrel (pr1 G) := pr12 G.

Local Notation "x ≤ y" := (TRRG_edgerel _ x y)(at level 70).

Definition TRRG_root (G : TRRGraph) : pr1 G := pr122 G.

Definition TRRG_transitivity (G : TRRGraph) : istrans (TRRG_edgerel G) := pr12 (pr222 G).

(** Definition of [TRRGraph] homomorphisms [isTRRGhomo], isomorphisms [TRRGraphiso], and a proof that isomorphisms are equivalent to identities [TRRGraph_univalence] **)

Definition isTRRGhomo {G H : TRRGraph} (f : pr1 G → pr1 H) : UU :=
(∏ (x y : pr1 G), (x ≤ y) <-> (f x ≤ f y)) × (f (TRRG_root G) = TRRG_root H).

Lemma isaprop_isTRRGhomo {G H : TRRGraph} (f : pr1 G → pr1 H) : isaprop (isTRRGhomo f).
Proof.
  apply isapropdirprod.
  - repeat (apply impred ; intros). apply isapropdirprod.
    -- repeat (apply impred; intros; apply propproperty).
    -- repeat (apply impred; intros; apply propproperty).
  - apply setproperty.
Qed.

Lemma TRRGhomo_frompath (X Y : hSet) (G : TRRGraphData X) (H : TRRGraphData Y) (p : X = Y) :
transportf (λ x : hSet, TRRGraphData x) p G = H → @isTRRGhomo (X ,, G) (Y ,, H) (pr1weq (hSet_univalence _ _ p)).
Proof.
  simpl.
  induction p.
  simpl.
  unfold isTRRGhomo.
  intros q.
  split.
  - intros x y.
    rewrite -> idpath_transportf in q.
    split.
    rewrite -> q.
    intros P ; apply P.
    rewrite -> q.
    intros P ; apply P.
  - rewrite -> idpath_transportf in q.
    induction q.
    reflexivity.
Qed.

(* The lemma [helper] below is needed because of some buggy Coq behaviour - perhaps it can be eliminated with a different proof *)

Local Lemma helper (X : hSet) (E E' : X → X → hProp) (r r' : X) (isE : isTRR X E r) (isE' : isTRR X E' r') (q : E = E') (σ : r = r') : transportf (λ x : X → X → hProp, ∑ r : X, isTRR X x r) q (r ,, isE) = (r' ,, isE').
Proof.
  induction q.
  rewrite idpath_transportf.
  apply total2_paths_equiv.
  exists σ.
  simpl.
  apply (isaprop_isTRR X E r').
Qed.

Lemma TRRGhomo_topath (X Y : hSet) (G : TRRGraphData X) (H : TRRGraphData Y) (p : X = Y) : @isTRRGhomo (X ,, G) (Y ,, H) (pr1weq (hSet_univalence _ _ p)) → transportf (λ x : hSet, TRRGraphData x) p G = H.
Proof.
  induction p.
  rewrite -> idpath_transportf.
  intros P.
  unfold isTRRGhomo in P.
  simpl in P.
  destruct P as [π σ].
  assert (q : pr1 G = pr1 H).
  {
    use funextfun.
    unfold homot.
    intros x.
    use funextfun.
    unfold homot.
    intros y.
    apply (hPropUnivalence (pr1 G x y) (pr1 H x y) (pr1 (π x y)) (pr2 (π x y))).
  }
  apply total2_paths_equiv.
  exists q.
  apply (helper X (pr1 G) (pr1 H) (pr12 G) (pr12 H) _ _ q σ).
Qed.

Definition TRRGraphiso (G H : TRRGraph) : UU := ∑ (f : pr1 G ≃ pr1 H), isTRRGhomo f.

Local Notation "G ≅ H" := (TRRGraphiso G H).

Theorem TRRGraph_univalence (G H : TRRGraph) : (G = H) ≃ (G ≅ H).
Proof.
    { intermediate_weq (G ╝ H).
      { apply total2_paths_equiv. }
      { use weqbandf.
        { apply (hSet_univalence (pr1 G) (pr1 H)). }
        { intro p. simpl. apply weqimplimpl.
           - intros q. apply (TRRGhomo_frompath (pr1 G) (pr1 H) (pr2 G) (pr2 H) p q).
           - intros q. apply (TRRGhomo_topath (pr1 G) (pr1 H) (pr2 G) (pr2 H) p q).
           - apply (isaset_TRRGraphData (pr1 H)).
           - apply (isaprop_isTRRGhomo).
         } } }
Qed.

Definition selfedge (G : TRRGraph) (x : pr1 G) : pr1 (pr2 G) x x
  := (pr1 (pr2 (pr2 (pr2 G))) x).

(** Definition of trees as a subtype [Tree] of [TRRGraph] and proof of univalence for trees [Tree_univalence] **)

Definition DownwardClosure {G : TRRGraph} (x : pr1 G) : UU :=
  ∑ y : pr1 G, y ≤ x.


Definition antisymmetric {G :TRRGraph} (y z : pr1 G) : UU :=
  (y ≤ z) × (z ≤ y) → (z = y).

Definition total {G : TRRGraph} (y z : pr1 G) : hProp :=
  (y ≤ z) ∨ (z ≤ y).

Definition isatree (G : TRRGraph) : UU :=
  ∏ (x : pr1 G) (y z : DownwardClosure x), antisymmetric (pr1 y) (pr1 z) × total (pr1 y) (pr1 z).

Lemma isaprop_isatree (G : TRRGraph) : isaprop (isatree G).
Proof.
  apply impred.
  intros t ; apply impred.
  intros x ; apply impred.
  intros y ; apply isapropdirprod.
  - apply impred.
    intros P.
    apply setproperty.
  - apply propproperty.
Qed.

Definition Tree : UU :=  ∑ G : TRRGraph, isatree G.

Definition Tree_iso (T1 T2 : Tree) : UU := pr1 T1 ≅ pr1 T2.

Theorem Tree_univalence (T1 T2 : Tree) : (T1 = T2) ≃ (Tree_iso T1 T2).
Proof.
  set (P := λ G, λ H, TRRGraph_univalence G H).
  set (Q := λ G, (isatree G ,, isaprop_isatree G)).
  apply (substructure_univalence _ _ P Q T1 T2).
Qed.

(** Definition of branches ("upward closures") for [Tree]s as a tree [Up x] for a point x of T **)

Definition Upw_underlying (T : Tree) (x : pr11 T) := ∑ (y : pr11 T), x ≤ y.

Lemma isaset_Upw_underlying (T : Tree) (x : pr11 T) : isaset (Upw_underlying T x).
Proof.
  apply isaset_total2.
  apply setproperty.
  intros y.
  apply hProp_to_hSet.
Qed.

Definition Upw (T : Tree) (x : pr11 T) : hSet :=
  (∑ (y : pr11 T), pr121 T x y) ,, (isaset_Upw_underlying T x).

Definition Upw_E (T : Tree) (x : pr11 T) (y z : Upw T x) : hProp
  := pr121 T (pr1 y) (pr1 z).

Definition Upw_to_RootedGraph (T : Tree) (x : pr11 T) : RootedGraph
  := Upw T x ,, Upw_E T x ,, (x ,, selfedge (pr1 T) x).

Lemma Upw_reflexive (T : Tree) (x : pr11 T) :
  ∏ (y : pr1 (Upw_to_RootedGraph T x)), pr12 (Upw_to_RootedGraph T x) y y.
Proof.
  intros y.
  simpl.
  unfold Upw_E.
  exact (selfedge (pr1 T) (pr1 y)).
Qed.

Lemma Upw_transitive (T : Tree) (x : pr11 T) :
  ∏ y z w, (Upw_E T x) y z → (Upw_E T x) z w → (Upw_E T x) y w.
Proof.
  intros y z w P Q.
  exact (TRRG_transitivity (pr1 T) (pr1 y) (pr1 z) (pr1 w) P Q).
Qed.

Lemma Upw_rooted (T : Tree) (x : pr11 T) : ∏ y, (Upw_E T x) (x ,, selfedge (pr1 T)  x) y.
Proof.
  intros y.
  exact (pr2 y).
Qed.

Definition Upw_to_TRRGraph (T : Tree) (x : pr11 T) : TRRGraph :=
  pr1 (Upw_to_RootedGraph T x) ,, pr12 (Upw_to_RootedGraph T x) ,, pr22 (Upw_to_RootedGraph T x) ,, Upw_reflexive T x ,, Upw_transitive T x ,, Upw_rooted T x.

Lemma isatree_Upw (T : Tree) (x : pr11 T) : isatree (Upw_to_TRRGraph T x).
Proof.
  unfold isatree. intros a. intros y z. simpl.
  set (zzz := ((pr1 (pr1 z)))). set (zz := (pr1 z)).
  set (yyy := ((pr1 (pr1 y)))). set (yy := (pr1 y)).
  assert (Eya : pr121 T yyy (pr1 a)).
     {
       unfold DownwardClosure in y. destruct y as [y σ]. simpl. apply σ.
     }
     assert (Eza : pr121 T zzz (pr1 a)).
     {
       unfold DownwardClosure in z. destruct z as [z σ]. simpl. apply σ.
     }
  split.
  -  simpl.
     unfold antisymmetric.
     intros X.
     destruct X as [yz zy].
     assert (L1 : zzz = yyy).
     {
       simpl in a.
       apply (pr1 (pr2 (T) (pr1 a) (yyy ,, Eya) (zzz ,, Eza)) (yz ,, zy)).
     }
     assert (p : pr1 zz = pr1 yy).
     {
       apply L1.
     }
     unfold Upw_to_TRRGraph in zz.
     unfold Upw_to_TRRGraph in yy.
     simpl in zz.
     simpl in yy.
     assert (q : pr2 zz = transportb (λ w, pr121 T x w) p (pr2 yy)).
     {
       apply proofirrelevance.
       apply (pr2 (pr121 T x (pr1 zz))).
     }
     apply (total2_paths_b p q).
  -  assert (L : pr121 T yyy zzz ∨ pr121 T zzz yyy).
     {
       apply (pr2 ((pr2 (T)) (pr1 a) (yyy ,, Eya) (zzz ,, Eza))).
     }
     apply L.
Qed.

Definition Up {T : Tree} (x : pr11 T) : Tree := (Upw_to_TRRGraph T x ,, isatree_Upw T x).

(** Definition of rigid [isrigid] and superrigid [issuperrigid] trees **)

Definition isrigid (T : Tree) : UU
  := iscontr (T = T).

Lemma isaprop_isrigid (T : Tree) : isaprop (isrigid T).
Proof.
  unfold isrigid.
  apply isapropiscontr.
Qed.

Definition issuperrigid (T : Tree) : UU
  := isrigid T × (∏ (x : pr11 T), isrigid (Up x)).

Lemma isaprop_issuperrigid (T : Tree) : isaprop (issuperrigid T).
Proof.
  unfold issuperrigid.
  apply isapropdirprod.
  apply isaprop_isrigid.
  apply impred.
  intros t.
  apply isaprop_isrigid.
Qed.

(** Definition of bi-well-founded trees (well-founded both "up" and "down") [Tree_isWellFounded] **)

Definition isWellFoundedUp (T : Tree) : hProp
  := hasSmallest (pr121 T).

Definition hasLargest {X : UU} (R : hrel X) : hProp
  := ∀ S : hsubtype X, (∃ x, S x) ⇒ ∃ x:X, S x ∧ ∀ y:X, S y ⇒ R y x.

Definition isWellFoundedDown (T : Tree) := hasLargest (pr121 T).

Definition Tree_isWellFounded (T : Tree) := (isWellFoundedUp T) × (isWellFoundedDown T).

Lemma isaprop_Tree_isWellFounded (T : Tree) : isaprop (Tree_isWellFounded T).
Proof.
  apply isapropdirprod.
  apply propproperty.
  apply propproperty.
Qed.

(** The definition of pre-ZF structures [preZFS].

   [preZFS] is classically equivalent to the [ZFS] we define below but, as far as we can tell,
   constructively inequivalent.

 **)

Definition ispreZFS (T : Tree) : UU := (Tree_isWellFounded T) × (issuperrigid T).

Lemma isaprop_ispreZFS (T : Tree) : isaprop (ispreZFS T).
Proof.
  apply isapropdirprod.
  apply (isaprop_Tree_isWellFounded T).
  apply (isaprop_issuperrigid T).
Qed.

Definition preZFS : UU := ∑ (T : Tree), ispreZFS T.

Definition Ve (X : preZFS) : hSet := pr111 X.
Coercion Ve : preZFS >-> hSet.

Definition Ed (X : preZFS) : (Ve X) → (Ve X) → hProp := pr1 (pr2 (pr1 (pr1 X))).

Definition root (X : preZFS) : Ve X := pr1 (pr2 (pr2 (pr1 (pr1 X)))).

Lemma preZFS_isrigid (X : preZFS) : iscontr (X = X).
Proof.
  apply (pr1contr_to_contr _ (λ x, (ispreZFS x ,, isaprop_ispreZFS x)) X).
  exact (pr122 X).
Qed.

Theorem isaset_preZFS : isaset preZFS.
Proof.
  simpl.
  unfold isaset.
  unfold isaprop.
  simpl.
  intros x y p.
  induction p.
  intros q.
  apply (hlevelntosn 0 (x = x) (preZFS_isrigid x) (idpath x) q).
Qed.

Definition preZFS_iso (X Y : preZFS) : UU := Tree_iso (pr1 X) (pr1 Y).

Theorem preZFS_univalence (X Y : preZFS) : (X = Y) ≃ (preZFS_iso X Y).
Proof.
  set (P := λ x, λ y, Tree_univalence x y).
  set (Q := λ x, (ispreZFS x ,, isaprop_ispreZFS x)).
  exact (substructure_univalence _ _ P Q X Y).
Qed.

(*** End of Basic Definitions ***)

(*** Definition of ZFS ***)

(** Contents **)

(**
-Upward Closure ("Branch") of a node x in a pre-ZF structure T
-Proof that it is a pre-ZF structure [Branch]
**)

Definition preZFS_Branch (T : preZFS) (x : T) : Tree := Up x.

Definition preZFS_Branch_hsubtype_tohsubtype (T : preZFS) (x : T) (S : hsubtype (pr11 (preZFS_Branch T x))) : hsubtype (pr111 T)
  := λ t, ∃ e, S (t ,, e).

(** REMARK : The definition [preZFS_Branch_hsubtype_tohsubtype] probably does not need to be truncated. One can define it without truncation and prove the lemmas that it is a proposition. **)

Definition hsubtype_to_preZFS_Branch_hsubtype (T : preZFS) (x : T) (S : hsubtype (pr111 T)) : hsubtype (pr11 (preZFS_Branch T x))
  := λ z, S (pr1 z) ∧ Ed T x (pr1 z).

Lemma Branch_to_subtype (T : preZFS) (x : T) (S : hsubtype (pr11 (preZFS_Branch T x)))
  : hsubtype_to_preZFS_Branch_hsubtype T x (preZFS_Branch_hsubtype_tohsubtype T x S) = S.
Proof.
  apply (funextfunPreliminaryUAH univalenceAxiom (pr11 (preZFS_Branch T x)) hProp (hsubtype_to_preZFS_Branch_hsubtype T x (preZFS_Branch_hsubtype_tohsubtype T x S)) S).
  unfold homot.
  intros y.
  unfold preZFS_Branch_hsubtype_tohsubtype.
  unfold hsubtype_to_preZFS_Branch_hsubtype.
  simpl.
  assert (ES : ((∃ e : Ed T x (pr1 y), S (pr1 y,, e)) ∧ Ed T x (pr1 y)) -> S y).
  {
    intros X.
    destruct X as [ε e].
    apply (ε (S y)).
    intros X.
    destruct y.
    destruct X as [y z].
    simpl in z.
    simpl in y.
    assert ( p : y = pr2 ).
    apply propproperty.
    rewrite <- p.
    apply z.
  }
  assert (SE : ((∃ e : Ed T x (pr1 y), S (pr1 y,, e)) ∧ Ed T x (pr1 y)) <- S y).
  {
    intros X.
    simpl.
    unfold ishinh_UU.
    split.
    - intros P Q.
      apply Q.
      exists (pr2 y).
      apply X.
    - apply (pr2 y).
  }
  apply (hPropUnivalence ((∃ e : Ed T x (pr1 y), S (pr1 y,, e)) ∧ Ed T x (pr1 y)) (S y) ES SE).
Qed.


Lemma fromBranch_hsubtype {T : preZFS} {x : T} {S : hsubtype (pr11 (preZFS_Branch T x))} {t :pr11 (preZFS_Branch T x)} (s : S t)
  : preZFS_Branch_hsubtype_tohsubtype T x S (pr1 t).
Proof.
  unfold preZFS_Branch_hsubtype_tohsubtype.
  simpl.
  unfold ishinh_UU.
  intros P X.
  apply X.
  exists (pr2 t).
  apply s.
Qed.

Lemma toBranch_hsubtype {T : preZFS} {x : T} {S : hsubtype (pr111 T)} {t : pr111 T} (e : Ed T x t) (s : S t)
  : hsubtype_to_preZFS_Branch_hsubtype T x S (t ,, e).
Proof.
  unfold hsubtype_to_preZFS_Branch_hsubtype.
  simpl.
  split.
  apply s.
  apply e.
Qed.

Lemma preZFS_Branch_isWellFounded (T : preZFS) (x : T) : Tree_isWellFounded (preZFS_Branch T x).
Proof.
  unfold Tree_isWellFounded.
  split.
  - unfold isWellFoundedUp.
    intros S.
    set (SS := preZFS_Branch_hsubtype_tohsubtype T x S).
    intros X.
    assert (wfunder : Tree_isWellFounded (pr1 T)).
    {
      apply (pr12 T).
    }
    unfold Tree_isWellFounded in wfunder.
    unfold isWellFoundedUp in wfunder.
    unfold hasSmallest in wfunder.
    apply pr1 in wfunder.
    simpl in wfunder.
    set (L1 := wfunder SS).
    assert (L2 : (∃ x : pr11 (preZFS_Branch T x), S x) → ishinh_UU (∑ y : pr111 T, SS y)).
    {
      intros P.
      simpl in P.
      apply (P (ishinh (∑ y : pr111 T, SS y))).
      intros X1.
      destruct X1 as [te s].
      destruct te as [t e].
      simpl.
      unfold ishinh_UU.
      intros Q X1.
      apply X1.
      exists t.
      apply (fromBranch_hsubtype s).
    }
    apply L2 in X.
    apply L1 in X.
    apply (X (∃ x0 : pr11 (preZFS_Branch T x), S x0 ∧ (∀ y : pr11 (preZFS_Branch T x), S y ⇒ pr121 (preZFS_Branch T x) x0 y))).
    intros Y.
    destruct Y as [t [s π]].
    assert (e : Ed T x t).
    {
      unfold SS in s.
      unfold preZFS_Branch_hsubtype_tohsubtype in s.
      apply (s (Ed T x t)).
      intros Y.
      destruct Y as [τ ξ].
      apply τ.
    }
    assert (L4 : S (t ,, e)).
    {
      rewrite <- (Branch_to_subtype T x S).
      apply (toBranch_hsubtype e s).
    }
    simpl.
    unfold ishinh_UU.
    intros P Y.
    apply Y.
    exists (t ,, e).
    split.
    -- apply L4.
    -- intros xx Q.
       unfold Upw_E.
       simpl.
       apply π.
       unfold SS.
       simpl.
       unfold ishinh_UU.
       intros R Z.
       apply Z.
       exists (pr2 xx).
       apply Q.
  - unfold isWellFoundedDown.
    intros S.
    set (SS := preZFS_Branch_hsubtype_tohsubtype T x S).
    intros X.
    set (wfunder := pr212 T).
    unfold isWellFoundedDown in wfunder.
    unfold hasLargest in wfunder.
    simpl in wfunder.
    set (L1 := wfunder SS).
    assert (L2 : (∃ x : pr11 (preZFS_Branch T x), S x) → ishinh_UU (∑ y : pr111 T, SS y)).
    {
      intros Y.
      simpl in Y.
      apply (Y (ishinh (∑ y : pr111 T, SS y))).
      intros Z.
      destruct Z as [te s].
      destruct te as [t e].
      simpl.
      unfold ishinh_UU.
      intros P W.
      apply W.
      exists t.
      apply (fromBranch_hsubtype s).
    }
    apply L2 in X.
    apply L1 in X.
    apply (X (∃ xx : pr11 (preZFS_Branch T x), S xx ∧ (∀ y : pr11 (preZFS_Branch T x), S y ⇒ pr121 (preZFS_Branch T x) y xx))).
    intros Y.
    destruct Y as [t [s π]].
    assert (e : Ed T x t).
    {
      unfold SS in s.
      unfold preZFS_Branch_hsubtype_tohsubtype in s.
      apply (s (Ed T x t)).
      intros Y.
      destruct Y as [τ ξ].
      apply τ.
    }
    assert (L4 : S (t ,, e)).
    {
      rewrite <- (Branch_to_subtype T x S).
      apply (toBranch_hsubtype e s).
    }
    simpl.
    unfold ishinh_UU.
    intros P Y.
    apply Y.
    exists (t ,, e).
    split.
    -- apply L4.
    -- intros xx Q.
       unfold Upw_E.
       simpl.
       apply π.
       unfold SS.
       simpl.
       unfold ishinh_UU.
       intros R Z.
       apply Z.
       exists (pr2 xx).
       apply Q.
Qed.

Lemma iscontrauto_Tree_TRRGraph (T : Tree) : isrigid T → iscontr ((pr1 T) = (pr1 T)).
Proof.
  apply (@contr_to_pr1contr _ (λ x, (isatree x ,, isaprop_isatree x)) T).
Qed.

Definition Up_to_Up (T : Tree) (x : pr11 T) (y : pr11 (Up x)) :
  pr1 (Upw_to_TRRGraph T (pr1 y)) → pr1 (Upw_to_TRRGraph (Up x) y).
Proof.
    simpl.
    intros X.
    induction X as [t π].
    induction y as [y σ].
    exact ((t ,, ((pr122 (pr221 T)) x y t σ π)) ,, π).
Defined.

Definition Up_to_Up_inv (T : Tree) (x : pr11 T) (y : pr11 (Up x)) :
  pr1 (Upw_to_TRRGraph (Up x) y) → pr1 (Upw_to_TRRGraph T (pr1 y)).
Proof.
    simpl.
    intros X.
    induction X as [t π].
    induction y as [y σ].
    induction t as [tt θ].
    simpl.
    unfold Upw_E in π.
    simpl in π.
    exact (tt ,, π).
Defined.

Lemma isweq_Up_to_Up  (T : Tree) (x : pr11 T) (y : pr11 (Up x)): isweq (Up_to_Up T x y).
Proof.
  set (f := Up_to_Up T x y).
  set (g := Up_to_Up_inv T x y).
  assert (L : ∏ x, f (g x) = x).
  {
    intros z.
    unfold g ; unfold Up_to_Up_inv.
    unfold f ; unfold Up_to_Up.
    destruct z as [z π].
    apply total2_paths_equiv.
    assert (H : (pr1 z,, pr122 (pr221 T) x (pr1 y) (pr1 z) (pr2 y) π) = z).
    {
      apply total2_paths_equiv.
      exists (idpath (pr1 z)).
      apply propproperty.
    }
    exists H.
    apply propproperty.
  }
   assert (LL : ∏ x, g (f x) = x).
  {
    intros z.
    unfold g ; unfold Up_to_Up_inv.
    unfold f ; unfold Up_to_Up.
    reflexivity.
  }
  apply (@weq_iso _ _ _ _ LL L).
Qed.

Lemma isTRRGhomo_Up_to_Up (T : Tree) (x : pr11 T) (y : pr11 (Up x)) : isTRRGhomo (Up_to_Up T x y).
Proof.
  split.
  - intros xx yy.
    simpl.
    split.
    -- intros P ; apply P.
    -- intros P ; apply P.
  - simpl.
    unfold Up_to_Up.
    unfold selfedge.
    simpl.
    apply total2_paths_equiv.
    destruct y as [y π].
    simpl.
    assert (q : pr122 (pr221 T) x y y π (selfedge (pr1 T) y) = π).
    {
      apply propproperty.
    }
    rewrite -> q.
    exists (idpath (y ,, π)).
    apply propproperty.
Qed.


Lemma UpUpid  (T : Tree) (x : pr11 T) (y : pr11 (Up x)) :
  pr1 (Up (pr1 y)) = Upw_to_TRRGraph (Up x) y.
Proof.
  apply TRRGraph_univalence.
  exists (weqpair (Up_to_Up T x y) (isweq_Up_to_Up T x y)).
  apply (isTRRGhomo_Up_to_Up T x y).
Qed.


Lemma preZFS_Branch_issuperrigid (T : preZFS) (x : T) : issuperrigid (preZFS_Branch T x).
 Proof.
  split.
  - apply (pr1contr_to_contr _ (λ x, (isatree x ,, isaprop_isatree x)) (preZFS_Branch T x)).
    apply (iscontrauto_Tree_TRRGraph (Up x) ((pr222 T) x)).
  - intros y.
    apply (pr1contr_to_contr _ (λ x, (isatree x ,, isaprop_isatree x)) (Up y)).
    simpl.
    unfold preZFS_Branch.
    unfold preZFS_Branch in y.
    rewrite <- UpUpid.
    apply (iscontrauto_Tree_TRRGraph (Up (pr1 y)) ((pr222 T) (pr1 y))).
Qed.

Definition Branch (T : preZFS) (x : T) : preZFS :=
  preZFS_Branch T x ,, preZFS_Branch_isWellFounded T x ,, preZFS_Branch_issuperrigid T x.

(** The definition of [ZFS] as a subtype of [preZFS] consisting of those pre-ZF structures each of whose branches have uniqe representatives [hasuniquerepbranch] **)

Definition hasuniquerepbranch (T : preZFS) : UU
  := ∏ (x y : T), (Branch T x) = (Branch T y) → x = y.

Lemma isaprop_hasuniquerepbranch (T : preZFS) : isaprop (hasuniquerepbranch T).
Proof.
  repeat (apply impred ; intros).
  apply setproperty.
Qed.

Definition ZFS : UU := ∑ (X : preZFS), hasuniquerepbranch X.

Definition pr1ZFS (X : ZFS) : preZFS := pr1 X.
Coercion pr1ZFS : ZFS >-> preZFS.

Definition ZFS_iso (x y : ZFS) := preZFS_iso x y.

Theorem ZFS_univalence (x y : ZFS) : (x = y) ≃ (ZFS_iso x y).
Proof.
  set (P := λ x, λ y, preZFS_univalence x y).
  set (Q := λ x, (hasuniquerepbranch x ,, isaprop_hasuniquerepbranch x)).
  apply (substructure_univalence _ _ P Q x y).
Qed.

Theorem isaset_ZFS : isaset ZFS.
Proof.
  apply (isofhleveltotal2 2).
  - apply isaset_preZFS.
  - intros x.
     apply hlevelntosn.
     apply isaprop_hasuniquerepbranch.
Qed.

(*** End of Definition of ZFS ***)

(*** The Elementhood Relation ***)

(** Contents **)
(* - A proof that branches of ZF structures are ZF structures [ZFS_Branch_is_ZFS]
   - A definition of elementhood [ZFS_elementof] between ZF structures X and Y as the existence of an isomorphism between X and a branch of Y.
*)

Definition Branch_of_Branch_to_Branch {T : preZFS} (x : T) (y : Branch T x) :
  pr1 (Upw_to_TRRGraph (preZFS_Branch T x) y) → pr1 (Upw_to_TRRGraph (pr1 T) (pr1 y)).
Proof.
  simpl.
  intros X.
  induction X as [[e ε] π].
  simpl in e.
  simpl in π.
  unfold Upw_E in π.
  simpl in π.
  exact (e ,, π).
Defined.

Definition Branch_of_Branch_to_Branch_inv {T : preZFS} (x : T) (y : Branch T x) :
  pr1 (Upw_to_TRRGraph (pr1 T) (pr1 y)) → pr1 (Upw_to_TRRGraph (preZFS_Branch T x) y) :=
  λ X, ((pr1 X ,, pr12 (pr222 (pr11 T)) x (pr1 y) (pr1 X) (pr2 y) (pr2 X)) ,, pr2 X).


Definition isweq_Branch_of_Branch_to_Branch {T : preZFS} (x : T) (y : Branch T x) :
  isweq (Branch_of_Branch_to_Branch x y).
Proof.
  set (f := Branch_of_Branch_to_Branch x y).
  set (g := Branch_of_Branch_to_Branch_inv x y).
  assert (L : ∏ x, f (g x) = x).
  {
    intros z.
    unfold f ; unfold Branch_of_Branch_to_Branch.
    unfold g ; unfold Branch_of_Branch_to_Branch_inv.
    induction z as [z π].
    simpl.
    apply idpath.
  }
  assert (LL : ∏ x, g (f x) = x).
  {
    intros z.
    unfold f ; unfold Branch_of_Branch_to_Branch.
    unfold g ; unfold Branch_of_Branch_to_Branch_inv.
    simpl.
    induction z as [z π].
    apply total2_paths_equiv.
    assert (H : (pr1 z,, pr122 (pr221 (pr1 T)) x (pr1 y) (pr1 z) (pr2 y) π) = z).
    {
      apply total2_paths_equiv.
      exists (idpath (pr1 z)).
      apply propproperty.
    }
    exists H.
    apply propproperty.
  }
  apply (@weq_iso _ _ _ _ LL L).
Defined.

Lemma isTRRGhomo_Branch_of_Branch_to_Branch {T : preZFS} (x : T) (y : Branch T x) :
  isTRRGhomo (Branch_of_Branch_to_Branch x y).
Proof.
  split.
  - intros xx yy.
    simpl.
    split.
    -- intros P ; apply P.
    -- intros P ; apply P.
  - simpl.
    unfold Branch_of_Branch_to_Branch.
    unfold selfedge.
    simpl.
    apply total2_paths_equiv.
    destruct y as [y π].
    simpl.
    exists (idpath y).
    apply propproperty.
Qed.


Lemma Branch_of_Branch_eq_Branch {T : preZFS} (x : T) (y : Branch T x) :
  Branch (Branch T x) y = Branch T (pr1 y).
Proof.
  apply preZFS_univalence.
  unfold preZFS_iso.
  unfold Tree_iso.
  simpl.
  exact ((Branch_of_Branch_to_Branch x y ,, isweq_Branch_of_Branch_to_Branch x y) ,, isTRRGhomo_Branch_of_Branch_to_Branch x y).
Qed.

Theorem ZFS_Branch_is_ZFS (X : ZFS) (x : X) : hasuniquerepbranch (Branch X x).
Proof.
  unfold hasuniquerepbranch.
  intros y z.
  rewrite -> (Branch_of_Branch_eq_Branch x y).
  rewrite -> (Branch_of_Branch_eq_Branch x z).
  intros p.
  set (π := pr2 X).
  simpl in π.
  set (τ := π (pr1 y) (pr1 z) p).
  apply total2_paths_equiv.
  exists τ.
  apply propproperty.
Qed.


Definition ZFS_Branch (X : ZFS) (x : X) : ZFS :=
  (Branch X x ,, ZFS_Branch_is_ZFS X x).

Local Notation "T ↑ x" := (ZFS_Branch T x)(at level 40).

Local Notation "x ⊏ y" := ((pr121 (pr111 _)) x y)(at level 50).

Definition Root (X : ZFS) := pr122 (pr111 X).

Definition isapoint {X : ZFS} (x : X) := ¬ (x = Root X).

Lemma isaprop_isapoint {X : ZFS} (x : X) : isaprop (isapoint x).
Proof.
  apply impred.
  intros.
  apply isapropempty.
Qed.

Definition ZFS_elementof (X Y : ZFS) := ∑ (a : Y), (isapoint a) × (X = Y ↑ a).

Lemma isaprop_ZFS_elementof (X Y : ZFS) : isaprop (ZFS_elementof X Y).
Proof.
  apply invproofirrelevance.
  unfold isProofIrrelevant.
  intros z w.
  unfold ZFS_elementof in z.
  unfold ZFS_elementof in w.
  destruct z as [z [ ispp p]].
  destruct w as [w [ ispq q]].
  set (r := (! q) @ p).
  apply total2_paths_equiv in r.
  destruct r as [r ρ].
  set (s := (pr2 Y w z r)).
  simpl in ρ.
  apply (total2_paths_hProp_equiv (λ y : Y, (isapoint y × X = Y ↑ y) ,, @isapropdirprod _ _ (isaprop_isapoint y) (isaset_ZFS X (Y ↑ y))) (z,, (ispp,, p)) (w,, (ispq,, q))).
  simpl.
  apply (! s).
Qed.

Local Notation "x ∈ y" := (ZFS_elementof x y)(at level 30).

(*** End of The Elementhood Relation ***)
