(** Pullbacks defined in terms of limits *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require        UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

Section def_pb.

Variable C : precategory.
Variable hs: has_homsets C.

Local Open Scope stn.
Definition One : three := ● 0.
Definition Two : three := ● 1.
Definition Three : three := ● 2.

Definition pullback_graph : graph.
Proof.
  exists three.
  use three_rec.
  - apply three_rec.
    + apply empty.
    + apply unit.
    + apply empty.
  - apply (λ _, empty).
  - apply three_rec.
    + apply empty.
    + apply unit.
    + apply empty.
Defined.

Definition pullback_diagram {a b c : C} (f : C ⟦b,a⟧) (g : C⟦c,a⟧) :
  diagram pullback_graph C.
Proof.
  exists (three_rec b a c).
  use three_rec_dep.
  - use three_rec_dep; simpl.
    + apply fromempty.
    + intro x; assumption.
    + apply fromempty.
  - intro x; apply fromempty.
  - use three_rec_dep; simpl.
    + apply fromempty.
    + intro x; assumption.
    + apply fromempty.
Defined.

Definition PullbCone {a b c : C} (f : C ⟦b,a⟧) (g : C⟦c,a⟧)
           (d : C) (f' : C ⟦d, b⟧) (g' : C ⟦d,c⟧)
           (H : f' · f = g'· g)
  : cone (pullback_diagram f g) d.
Proof.
  use mk_cone.
  - use three_rec_dep; try assumption.
    apply (f' · f).
  - use three_rec_dep; use three_rec_dep.
    + exact (Empty_set_rect _ ).
    + intro x; apply idpath.
    + exact (Empty_set_rect _ ).
    + exact (Empty_set_rect _ ).
    + exact (Empty_set_rect _ ).
    + exact (Empty_set_rect _ ).
    + exact (Empty_set_rect _ ).
    + intro x; apply (!H).
    + exact (Empty_set_rect _ ).
Defined.

Definition isPullback {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 · f = p2· g) : UU :=
    isLimCone (pullback_diagram f g) d (PullbCone f g d p1 p2 H).
(*
   ∏ e (h : e --> b) (k : e --> c)(H : h · f = k · g ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk · p1 = h)(hk · p2 = k))).
 *)

Definition mk_isPullback {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 · f = p2· g) :
  (∏ e (h : C ⟦e, b⟧) (k : C⟦e,c⟧)(Hk : h · f = k · g ),
      iscontr (total2 (fun hk : C⟦e,d⟧ => dirprod (hk · p1 = h)(hk · p2 = k))))
  →
  isPullback f g p1 p2 H.
Proof.
  intros H' x cx; simpl in *.
  set (H1 := H' x (coneOut cx One) (coneOut cx Three) ).
  simple refine (let p : coneOut cx One · f = coneOut cx Three · g := _ in _ ).
  { eapply pathscomp0; [apply (coneOutCommutes cx One Two tt)|].
    apply pathsinv0, (coneOutCommutes cx Three Two tt). }
  set (H2 := H1 p).
  mkpair.
  + exists (pr1 (pr1 H2)).
    use three_rec_dep.
    * apply (pr1 (pr2 (pr1 H2))).
    * simpl.
      change (three_rec_dep (λ n, C⟦d,_⟧) _ _ _ _) with (p1 · f).
      rewrite assoc.
      eapply pathscomp0.
        eapply cancel_postcomposition, (pr2 (pr1 H2)).
      apply (coneOutCommutes cx One Two tt).
    * apply (pr2 (pr2 (pr1 H2))).
  + abstract (intro t; apply subtypeEquality;
              [ intro; apply impred; intro; apply hs
              | destruct t as [t p0];
                apply path_to_ctr; split; [ apply (p0 One) | apply (p0 Three) ]]).
Defined.

(*
Lemma isaprop_isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2 · g) :
       isaprop (isPullback f g p1 p2 H).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.
*)

Definition Pullback {a b c : C} (f : C⟦b, a⟧)(g : C⟦c, a⟧) :=
     LimCone (pullback_diagram f g).

Definition mk_Pullback {a b c : C} (f : C⟦b, a⟧)(g : C⟦c, a⟧)
    (d : C) (p1 : C⟦d,b⟧) (p2 : C ⟦d,c⟧)
    (H : p1 · f = p2 · g)
    (ispb : isPullback f g p1 p2 H)
  : Pullback f g.
Proof.
  mkpair.
  - mkpair.
    + apply d.
    + use PullbCone; assumption.
  - apply ispb.
Defined.


(*
Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun pfg : total2 (λ p : C, (p --> b) × (p --> c)) =>
         total2 (fun H : pr1 (pr2 pfg) · f = pr2 (pr2 pfg) · g =>
        isPullback f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).
 *)

Definition Pullbacks := ∏ (a b c : C)(f : C⟦b, a⟧)(g : C⟦c, a⟧),
       Pullback f g.

Definition hasPullbacks := ∏ (a b c : C) (f : C⟦b, a⟧) (g : C⟦c, a⟧),
         ishinh (Pullback f g).


Definition PullbackObject {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}:
   Pullback f g -> C := λ H, lim H.
(* Coercion PullbackObject : Pullback >-> ob. *)

Definition PullbackPr1 {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
   (Pb : Pullback f g) : C⟦lim Pb, b⟧ := limOut Pb One.

Definition PullbackPr2 {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
   (Pb : Pullback f g) : C⟦lim Pb, c⟧ := limOut Pb Three.

Definition PullbackSqrCommutes {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
           (Pb : Pullback f g) :
  PullbackPr1 Pb · f = PullbackPr2 Pb · g .
Proof.
  eapply pathscomp0; [apply (limOutCommutes Pb One Two tt) |].
  apply (!limOutCommutes Pb Three Two tt) .
Qed.

Definition PullbackArrow {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
           (Pb : Pullback f g) e (h : C⟦e, b⟧) (k : C⟦e, c⟧)(H : h · f = k · g)
  : C⟦e, lim Pb⟧.
Proof.
  now use limArrow; use PullbCone.
Defined.

Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
   (Pb : Pullback f g) e (h : C⟦e, b⟧) (k : C⟦e, c⟧)(H : h · f = k · g) :
   PullbackArrow Pb e h k H · PullbackPr1 Pb = h.
Proof.
  refine (limArrowCommutes Pb e _ One).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
   (Pb : Pullback f g) e (h : C⟦e, b⟧) (k : C⟦e, c⟧)(H : h · f = k · g) :
   PullbackArrow Pb e h k H · PullbackPr2 Pb = k.
Proof.
  refine (limArrowCommutes Pb e _ Three).
Qed.

Lemma PullbackArrowUnique {a b c d : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧)
     (Pb : Pullback f g)
     e (h : C⟦e, b⟧) (k : C⟦e, c⟧)
     (Hcomm : h · f = k · g)
     (w : C⟦e, PullbackObject Pb⟧)
     (H1 : w · PullbackPr1 Pb  = h) (H2 : w · PullbackPr2 Pb = k) :
  w = PullbackArrow Pb _ h k Hcomm.
Proof.
  apply path_to_ctr.
  use three_rec_dep; try assumption.
  set (X:= limOutCommutes Pb Three Two tt).
  eapply pathscomp0.
    eapply maponpaths, pathsinv0, X.
  simpl.
  rewrite assoc.
  eapply pathscomp0.
    apply cancel_postcomposition, H2.
  apply (!Hcomm).
Qed.

Definition isPullback_Pullback {a b c : C} {f : C⟦b, a⟧}{g : C⟦c, a⟧}
   (P : Pullback f g) :
  isPullback f g (PullbackPr1 P) (PullbackPr2 P) (PullbackSqrCommutes P).
Proof.
  apply mk_isPullback.
  intros e h k HK.
  mkpair.
  - mkpair.
    + apply (PullbackArrow P _ h k HK).
    + split.
      * apply PullbackArrow_PullbackPr1.
      * apply PullbackArrow_PullbackPr2.
  - intro t.
    apply subtypeEquality.
    + intro. apply isapropdirprod; apply hs.
    + destruct t as [t p]. simpl.
      refine (PullbackArrowUnique _ _ P _ _ _ _ _ _ _ ).
      * apply e.
      * apply (pr1 p).
      * apply (pr2 p).
Qed.


(** ** Maps between pullbacks as special limits and
       direct formulation of pullbacks
*)

Lemma equiv_isPullback_1 {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
      (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 · f = p2· g) :
  limits.pullbacks.isPullback f g p1 p2 H -> isPullback f g p1 p2 H.
Proof.
  intro X.
  intros R cc.
  set (XR := limits.pullbacks.mk_Pullback _ _ _ _ _ _ X).
  mkpair.
  - mkpair.
    + use (pullbacks.PullbackArrow XR).
      * apply (coneOut cc One).
      * apply (coneOut cc Three).
      * abstract (
        assert (XRT := coneOutCommutes cc Three Two tt); simpl in XRT;
        eapply pathscomp0; [| apply (!XRT)]; clear XRT;
        assert (XRT := coneOutCommutes cc One Two tt); simpl in XRT;
        eapply pathscomp0; [| apply (XRT)]; apply idpath
         ).
    + use three_rec_dep.
      * abstract (apply (pullbacks.PullbackArrow_PullbackPr1 XR)).
      * abstract (simpl;
        change (three_rec_dep (λ n, C⟦d,_⟧) _ _ _ _) with (p1 · f);
        rewrite assoc;
        rewrite  (limits.pullbacks.PullbackArrow_PullbackPr1 XR);
        assert (XRT := coneOutCommutes cc One Two tt); simpl in XRT;
        eapply pathscomp0; [| apply (XRT)]; apply idpath).
      * abstract (apply (limits.pullbacks.PullbackArrow_PullbackPr2 XR)).
  - abstract (
    intro t;
    apply subtypeEquality;
    [intro; apply impred; intro; apply hs |];
    simpl; destruct t as [t HH];  simpl in *;
    apply limits.pullbacks.PullbackArrowUnique;
    [ apply (HH One) | apply (HH Three)] ).
Qed.

Definition equiv_Pullback_1 {a b c : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧) :
  limits.pullbacks.Pullback f g -> Pullback f g.
Proof.
  intros X.
  exact (mk_Pullback
           f g (limits.pullbacks.PullbackObject X)
           (limits.pullbacks.PullbackPr1 X)
           (limits.pullbacks.PullbackPr2 X)
           (limits.pullbacks.PullbackSqrCommutes X)
           (equiv_isPullback_1 _ _ _ _ _ (limits.pullbacks.isPullback_Pullback X))).
Defined.

Definition equiv_Pullbacks_1: @limits.pullbacks.Pullbacks C -> Pullbacks.
Proof.
  intros X' a b c f g.
  set (X := X' a b c f g).
  exact (mk_Pullback
           f g (limits.pullbacks.PullbackObject X)
           (limits.pullbacks.PullbackPr1 X)
           (limits.pullbacks.PullbackPr2 X)
           (limits.pullbacks.PullbackSqrCommutes X)
           (equiv_isPullback_1 _ _ _ _ _ (limits.pullbacks.isPullback_Pullback X))).
Defined.

Lemma equiv_isPullback_2 {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
      (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 · f = p2· g) :
  limits.pullbacks.isPullback f g p1 p2 H <- isPullback f g p1 p2 H.
Proof.
  intro X.
  set (XR := mk_Pullback _ _ _ _ _  _ X).
  intros R k h HH.
  mkpair.
  - mkpair.
    use (PullbackArrow XR); try assumption.
    split.
    + apply (PullbackArrow_PullbackPr1 XR).
    + apply (PullbackArrow_PullbackPr2 XR).
  - abstract (
    intro t; apply subtypeEquality;
    [ intro; apply isapropdirprod; apply hs |] ;
    induction t as [x Hx]; simpl in * ;
    use (PullbackArrowUnique _ _ XR);
    [apply R | apply (pr1 Hx) | apply (pr2 Hx) ]
    ).
Qed.

Definition equiv_Pullback_2 {a b c : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧) :
  limits.pullbacks.Pullback f g <- Pullback f g.
Proof.
  intros X.
  exact (limits.pullbacks.mk_Pullback
           f g
           (PullbackObject X)
           (PullbackPr1 X)
           (PullbackPr2 X)
           (PullbackSqrCommutes X)
           (equiv_isPullback_2 _ _ _ _ _ (isPullback_Pullback X))).
Defined.

Definition equiv_Pullbacks_2 : @limits.pullbacks.Pullbacks C <- Pullbacks.
Proof.
  intros X' a b c f g.
  set (X := X' a b c f g).
  exact (limits.pullbacks.mk_Pullback
           f g
           (PullbackObject X)
           (PullbackPr1 X)
           (PullbackPr2 X)
           (PullbackSqrCommutes X)
           (equiv_isPullback_2 _ _ _ _ _ (isPullback_Pullback X))).
Defined.

Definition identity_is_Pullback_input {a b c : C}{f : C⟦b, a⟧} {g : C⟦c, a⟧} (Pb : Pullback f g) :
 total2 (fun hk : C⟦lim Pb, lim Pb⟧ =>
   dirprod (hk · PullbackPr1 Pb = PullbackPr1 Pb)(hk · PullbackPr2 Pb = PullbackPr2 Pb)).
Proof.
  exists (identity (lim Pb)).
  apply dirprodpair; apply id_left.
Defined.

(* was PullbackArrowUnique *)
Lemma PullbackArrowUnique' {a b c d : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧)
      (p1 : C⟦d, b⟧) (p2 : C⟦d, c⟧) (H : p1 · f = p2 · g) (P : isPullback f g p1 p2 H)
      (e : C) (h : C⟦e, b⟧) (k : C⟦e, c⟧) (Hcomm : h · f = k · g) (w : C⟦e, d⟧)
      (H1 : w · p1 = h) (H2 : w · p2 = k) :
  w =  (pr1 (pr1 (P e (PullbCone f g _ h k Hcomm)))).
Proof.
  apply path_to_ctr.
  use three_rec_dep; try assumption; simpl.
  change (three_rec_dep (λ n, C⟦d,_⟧) _ _ _ _) with (p1 · f).
  change (three_rec_dep (λ n, C⟦e,_⟧) _ _ _ _) with (h · f).
  now rewrite <- H1, assoc.
Qed.


Lemma PullbackEndo_is_identity {a b c : C}{f : C⟦b, a⟧} {g : C⟦c, a⟧} (Pb : Pullback f g)
      (k : C⟦lim Pb, lim Pb⟧) (kH1 : k · PullbackPr1 Pb = PullbackPr1 Pb)
      (kH2 : k · PullbackPr2 Pb = PullbackPr2 Pb) : identity (lim Pb) = k.
Proof.
  apply lim_endo_is_identity.
  use three_rec_dep.
  - apply kH1.
  - unfold limOut. simpl.
    assert (T:= coneOutCommutes (limCone Pb) Three Two tt).
    eapply pathscomp0. apply maponpaths. apply (!T).
    rewrite assoc.
    eapply pathscomp0. apply cancel_postcomposition.
       apply kH2.
       apply T.
 - assumption.
Qed.


Definition from_Pullback_to_Pullback {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
           (Pb Pb': Pullback f g) : C⟦lim Pb, lim Pb'⟧.
Proof.
  apply (PullbackArrow Pb' (lim Pb) (PullbackPr1 _ ) (PullbackPr2 _)).
  exact (PullbackSqrCommutes _ ).
Defined.


Lemma are_inverses_from_Pullback_to_Pullback {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
      (Pb Pb': Pullback f g) :
  is_inverse_in_precat (from_Pullback_to_Pullback Pb Pb') (from_Pullback_to_Pullback Pb' Pb).
Proof.
  split; apply pathsinv0;
  apply PullbackEndo_is_identity;
  rewrite <- assoc;
  unfold from_Pullback_to_Pullback;
  repeat rewrite PullbackArrow_PullbackPr1;
  repeat rewrite PullbackArrow_PullbackPr2;
  auto.
Qed.


Lemma isiso_from_Pullback_to_Pullback {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
      (Pb Pb': Pullback f g) : is_iso (from_Pullback_to_Pullback Pb Pb').
Proof.
  apply (is_iso_qinv _ (from_Pullback_to_Pullback Pb' Pb)).
  apply are_inverses_from_Pullback_to_Pullback.
Defined.


Definition iso_from_Pullback_to_Pullback {a b c : C} {f : C⟦b, a⟧} {g : C⟦c, a⟧}
           (Pb Pb': Pullback f g) : iso (lim Pb) (lim Pb') :=
  tpair _ _ (isiso_from_Pullback_to_Pullback Pb Pb').


(** pullback lemma *)

Section pullback_lemma.

Variables a b c d e x : C.
Variables (f : C⟦b, a⟧) (g : C⟦c, a⟧) (h : C⟦e, b⟧) (k : C⟦e, c⟧)
          (i : C⟦d, b⟧) (j : C⟦x, e⟧) (m : C⟦x, d⟧).
Hypothesis H1 : h · f = k · g.
Hypothesis H2 : m · i = j · h.
Hypothesis P1 : isPullback _ _ _ _ H1.
Hypothesis P2 : isPullback _ _ _ _ H2.

Lemma glueSquares : m · (i · f) = (j · k) · g.
Proof.
  rewrite assoc.
  rewrite H2.
  repeat rewrite <- assoc.
  rewrite H1.
  apply idpath.
Qed.

(*
Lemma isPullbackGluedSquare : isPullback (i · f) g m (j · k) glueSquares.
Proof.
  apply mk_isPullback.
  intros y p q.
  intro Hrt.
  assert (ex : (p· i)· f = q· g).
   { rewrite <- Hrt.
     rewrite assoc; apply idpath.
   }
  set (rt := P1 _ (p · i) q ex).
  set (Ppiq := pr1 (pr1 (rt))).
  assert (owiej : p · i = Ppiq · h).
   { apply pathsinv0. apply (pr1 (pr2 (pr1 rt))). }
  set (rt' := P2 _ p Ppiq owiej).
  set (awe := pr1 (pr1 rt')).
  assert (Hawe1 : awe · m = p).
   { exact (pr1 (pr2 (pr1 rt'))). }
  assert (Hawe2 : awe · (j · k) = q).
   { rewrite assoc.
     set (X := pr2 (pr2 (pr1 rt'))). simpl in X.
           unfold awe. rewrite X.
           exact (pr2 (pr2 (pr1 rt))).
   }
  exists (tpair _ awe (dirprodpair Hawe1 Hawe2)).
  intro t.
  apply subtypeEquality.
  - intro a0. apply isapropdirprod;
    apply hs.
  - simpl. destruct t as [t [Ht1 Ht2]].
    simpl in *.
    apply PullbackArrowUnique.
    + assumption.
    + apply PullbackArrowUnique.
      * rewrite <- Ht1.
        repeat rewrite <- assoc.
        rewrite H2.
        apply idpath.
      * rewrite <- assoc.
        assumption.
Qed.
 *)

End pullback_lemma.

Section Universal_Unique.

Hypothesis H : is_univalent C.


Lemma inv_from_iso_iso_from_Pullback (a b c : C) (f : C⟦b, a⟧) (g : C⟦c, a⟧)
  (Pb : Pullback f g) (Pb' : Pullback f g):
    inv_from_iso (iso_from_Pullback_to_Pullback Pb Pb') = from_Pullback_to_Pullback Pb' Pb.
Proof.
  apply pathsinv0.
  apply inv_iso_unique'.
  set (T:= are_inverses_from_Pullback_to_Pullback Pb Pb').
  apply (pr1 T).
Qed.

(*
Lemma isaprop_Pullbacks: isaprop Pullbacks.
Proof.
  apply impred; intro a;
  apply impred; intro b;
  apply impred; intro c;
  apply impred; intro f;
  apply impred; intro g;
  apply invproofirrelevance.
  intros Pb Pb'.
  apply subtypeEquality.
  - intro; apply isofhleveltotal2.
    + apply hs.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.
 *)

End Universal_Unique.

End def_pb.

Lemma Pullbacks_from_Lims (C : precategory) :
  Lims C -> Pullbacks C.
Proof.
  intros H a b c f g; apply H.
Defined.
