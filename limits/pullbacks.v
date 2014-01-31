
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.aux_lemmas_HoTT.
Require Import RezkCompletion.limits.terminal.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section def_pb.

Variable C : precategory.


Definition isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f == p2;; g) : UU :=
   forall e (h : e --> b) (k : e --> c)(H : h ;; f == k ;; g ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk ;; p1 == h)(hk ;; p2 == k))).

Lemma isaprop_isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f == p2 ;; g) :
       isaprop (isPullback f g p1 p2 H).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma PullbackArrowUnique {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f == p2;; g) 
     (P : isPullback f g p1 p2 H) e (h : e --> b) (k : e --> c)
     (Hcomm : h ;; f == k ;; g)
     (w : e --> d)
     (H1 : w ;; p1 == h) (H2 : w ;; p2 == k) :
     w == (pr1 (pr1 (P e h k Hcomm))).
Proof.
  set (T := tpair (fun hk : e --> d => dirprod (hk ;; p1 == h)(hk ;; p2 == k)) 
                    w (dirprodpair H1 H2)).
  set (T' := pr2 (P e h k Hcomm) T).
  exact (base_paths _ _ T').
Qed.


Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun pfg : total2 (fun p : C => dirprod (p --> b) (p --> c)) =>
         total2 (fun H : pr1 (pr2 pfg) ;; f == pr2 (pr2 pfg) ;; g =>
        isPullback f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).

Definition Pullbacks := forall (a b c : C)(f : b --> a)(g : c --> a),
       Pullback f g.

Definition hasPullbacks := forall (a b c : C) (f : b --> a) (g : c --> a),
         ishinh (Pullback f g).


Definition PullbackObject {a b c : C} {f : b --> a} {g : c --> a}: 
   Pullback f g -> C := fun H => pr1 (pr1 H).
Coercion PullbackObject : Pullback >-> ob.

Definition PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> b := pr1 (pr2 (pr1 Pb)).

Definition PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> c := pr2 (pr2 (pr1 Pb)).

Definition PullbackSqrCommutes {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : 
    PullbackPr1 Pb ;; f == PullbackPr2 Pb ;; g . 
Proof. 
  exact (pr1 (pr2 Pb)).
Qed.

Definition isPullback_Pullback {a b c : C} {f : b --> a}{g : c --> a} 
   (P : Pullback f g) : 
  isPullback f g (PullbackPr1 P) (PullbackPr2 P) (PullbackSqrCommutes P).
Proof.
  exact (pr2 (pr2 P)).
Qed.

Definition PullbackArrow {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f == k ;; g) : e --> Pb :=
   pr1 (pr1 (isPullback_Pullback Pb e h k H)).

Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f == k ;; g) :
   PullbackArrow Pb e h k H ;; PullbackPr1 Pb == h.
Proof.
  exact (pr1 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f == k ;; g) :
   PullbackArrow Pb e h k H ;; PullbackPr2 Pb == k.
Proof.
  exact (pr2 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.



Definition identity_is_Pullback_input {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) : 
 total2 (fun hk : Pb --> Pb => 
   dirprod (hk ;; PullbackPr1 Pb == PullbackPr1 Pb)(hk ;; PullbackPr2 Pb == PullbackPr2 Pb)).
Proof.
  exists (identity Pb).
  apply dirprodpair; apply id_left.
Defined.

Lemma PullbackEndo_is_identity {a b c : C}{f : b --> a} {g : c --> a}
   (Pb : Pullback f g) (k : Pb --> Pb) (kH1 : k ;; PullbackPr1 Pb == PullbackPr1 Pb)
                                       (kH2 : k ;; PullbackPr2 Pb == PullbackPr2 Pb) :
       identity Pb == k.
Proof.
  set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (hk ;; _ == _)(hk ;; _ == _))) k (dirprodpair kH1 kH2)).
  assert (H2 : identity_is_Pullback_input Pb == H1).
  - apply proofirrelevance.
    apply isapropifcontr.
    apply (isPullback_Pullback Pb).
    apply PullbackSqrCommutes.
  - apply (base_paths _ _ H2).
Qed.


Definition from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : Pb --> Pb'.
Proof.
  apply (PullbackArrow Pb' Pb (PullbackPr1 _ ) (PullbackPr2 _)).
  exact (PullbackSqrCommutes _ ).
Defined.


Lemma are_inverses_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : 
is_inverse_in_precat (from_Pullback_to_Pullback Pb Pb')
  (from_Pullback_to_Pullback Pb' Pb).
Proof.
  split; apply pathsinv0;
  apply PullbackEndo_is_identity;
  rewrite <- assoc;
  unfold from_Pullback_to_Pullback;
  repeat rewrite PullbackArrow_PullbackPr1;
  repeat rewrite PullbackArrow_PullbackPr2;
  auto.
Qed.


Lemma isiso_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : 
      is_isomorphism (from_Pullback_to_Pullback Pb Pb').
Proof.
  exists (from_Pullback_to_Pullback Pb' Pb).
  apply are_inverses_from_Pullback_to_Pullback.
Defined.


Definition iso_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : iso Pb Pb' :=
  tpair _ _ (isiso_from_Pullback_to_Pullback Pb Pb').


(** pullback lemma *)

Section pullback_lemma.

Variables a b c d e x : C.
Variables (f : b --> a) (g : c --> a) (h : e --> b) (k : e --> c)
          (i : d --> b) (j : x --> e) (m : x --> d).
Hypothesis H1 : h ;; f == k ;; g.
Hypothesis H2 : m ;; i == j ;; h.
Hypothesis P1 : isPullback _ _ _ _ H1.
Hypothesis P2 : isPullback _ _ _ _ H2.

Lemma glueSquares : m ;; (i ;; f) == (j ;; k) ;; g.
Proof.
  rewrite assoc.
  rewrite H2.
  repeat rewrite <- assoc.
  rewrite H1.
  apply idpath.
Qed.

Lemma isPullbackGluedSquare : isPullback (i ;; f) g m (j ;; k) glueSquares.
Proof.
  unfold isPullback.
  intros y p q.
  intro Hrt.
  assert (ex : (p;; i);; f == q;; g).
   { rewrite <- Hrt.
     rewrite assoc; apply idpath.
   }
  set (rt := P1 _ (p ;; i) q ex).
  set (Ppiq := pr1 (pr1 (rt))).
  assert (owiej : p ;; i == Ppiq ;; h).
   { apply pathsinv0. apply (pr1 (pr2 (pr1 rt))). }
  set (rt' := P2 _ p Ppiq owiej).
  set (awe := pr1 (pr1 rt')).
  assert (Hawe1 : awe ;; m == p).
   { exact (pr1 (pr2 (pr1 rt'))). }
  assert (Hawe2 : awe ;; (j ;; k) == q).
   { rewrite assoc.
     set (X := pr2 (pr2 (pr1 rt'))). simpl in X.
           unfold awe. rewrite X.
           exact (pr2 (pr2 (pr1 rt))). 
   }
  exists (tpair _ awe (dirprodpair Hawe1 Hawe2)).
  intro t.
  apply total2_paths_hProp.
  - intro a0. apply isapropdirprod;
    apply (pr2 (_ --> _)).
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

End pullback_lemma.

Section Universal_Unique.

Hypothesis H : is_category C.

Lemma isaprop_Pullbacks: isaprop Pullbacks.
Proof.
  apply impred; intro a;
  apply impred; intro b;
  apply impred; intro c;
  apply impred; intro f;
  apply impred; intro g;
  apply invproofirrelevance.
  intros Pb Pb'.
  apply total2_paths_hProp.
  - intro; apply isofhleveltotal2.
    + apply (pr2 (_ --> _)).
    + intros; apply isaprop_isPullback.
  - apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))). 
    rewrite transportf_dirprod, transportf_isotoid.
    change (inv_from_iso (iso_from_Pullback_to_Pullback Pb Pb'))
         with (from_Pullback_to_Pullback Pb' Pb).
    rewrite transportf_isotoid.
    change (inv_from_iso (iso_from_Pullback_to_Pullback Pb Pb'))
         with (from_Pullback_to_Pullback Pb' Pb).
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

End Universal_Unique.

End def_pb.
