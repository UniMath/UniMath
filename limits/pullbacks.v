
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.aux_lemmas_HoTT.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section def_pb.

Variable C : precategory.


Definition isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (f' : d --> c) (g' : d --> b) (H : f' ;; g == g';; f) : UU :=
   forall e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk ;; f' == k)(hk ;; g' == h))).

Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun pfg : total2 (fun p : C => dirprod (p --> c) (p --> b)) =>
         total2 (fun H : pr1 (pr2 pfg) ;; g == pr2 (pr2 pfg) ;; f =>
        isPullback f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).

Definition Pullbacks := forall (a b c : C)(f : b --> a)(g : c --> a),
       Pullback f g.

Definition hasPullbacks := forall (a b c : C) (f : b --> a) (g : c --> a),
         ishinh (Pullback f g).


Definition PullbackObject {a b c : C} {f : b --> a} {g : c --> a}: 
   Pullback f g -> C := fun H => pr1 (pr1 H).
Coercion PullbackObject : Pullback >-> ob.

Definition PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> c := pr1 (pr2 (pr1 Pb)).

Definition PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> b := pr2 (pr2 (pr1 Pb)).

Definition PullbackSqrCommutes {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : 
    PullbackPr1 Pb ;; g == PullbackPr2 Pb ;; f . 
Proof. 
  apply (pr1 (pr2 Pb)).
Qed.

Definition PullbackArrow {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) : e --> Pb :=
   pr1 (pr1 (pr2 (pr2 Pb) e h k H)).

Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) :
   PullbackArrow Pb e h k H ;; PullbackPr1 Pb == k.
Proof.
  apply (pr2 (pr1 (pr2 (pr2 Pb) e h k H))).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) :
   PullbackArrow Pb e h k H ;; PullbackPr2 Pb == h.
Proof.
  apply (pr2 (pr2 (pr1 (pr2 (pr2 Pb) e h k H)))).
Qed.



Definition identity_is_Pullback_input {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) : 
 total2 (fun hk : Pb --> Pb => 
   dirprod (hk ;; PullbackPr1 Pb == PullbackPr1 Pb)(hk ;; PullbackPr2 Pb == PullbackPr2 Pb)).
Proof.
  exists (identity Pb).
  apply (dirprodpair).
  apply id_left.
  apply id_left.
Defined.

Lemma PullbackEndo_is_identity {a b c : C}{f : b --> a} {g : c --> a}
   (Pb : Pullback f g) (k : Pb --> Pb) (kH1 : k ;; PullbackPr1 Pb == PullbackPr1 Pb)
                                       (kH2 : k ;; PullbackPr2 Pb == PullbackPr2 Pb) :
       identity Pb == k.
Proof.
  set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (hk ;; _ == _)(hk ;; _ == _))) k (dirprodpair kH1 kH2)).
  assert (H2 : identity_is_Pullback_input Pb == H1).
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 (pr2 Pb)).
  apply PullbackSqrCommutes.
(*  set (H:= pr2 (pr2 (pr2 (pr2 Pb)))).  simpl in H.
  set (HH:= H Pb (PullbackPr2 Pb) (PullbackPr1 Pb) (PullbackSqrCommutes Pb)).
  apply HH.
*)
  apply (base_paths _ _ H2).
Qed.


(*
Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun p =>
     total2 (fun f' : p --> c =>
     total2 (fun g' : p --> b =>
     total2 (fun H : f' ;; g == g' ;; f =>
        isPullback f g f' g' H)))).

Definition Pullbacks := forall (a b c : C)(f : b --> a)(g : c --> a),
       Pullback f g.

Definition hasPullbacks := forall (a b c : C) (f : b --> a) (g : c --> a),
         ishinh (Pullback f g).



Definition PullbackObject {a b c : C} {f : b --> a} {g : c --> a}: 
   Pullback f g -> C := fun H => pr1 H.
Coercion PullbackObject : Pullback >-> ob.

Definition PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> c := pr1 (pr2 Pb).

Definition PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : Pb --> b := pr1 (pr2 (pr2 Pb)).

Definition PullbackSqrCommutes {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) : 
    PullbackPr1 Pb ;; g == PullbackPr2 Pb ;; f . 
Proof. 
  apply (pr1 (pr2 (pr2 (pr2 Pb)))).
Qed.

Definition PullbackArrow {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) : e --> Pb :=
   pr1 (pr1 (pr2 (pr2 (pr2 (pr2 Pb))) e h k H)).

Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) :
   PullbackArrow Pb e h k H ;; PullbackPr1 Pb == k.
Proof.
  apply (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 Pb))) e h k H)))).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a} 
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f) :
   PullbackArrow Pb e h k H ;; PullbackPr2 Pb == h.
Proof.
  apply (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 Pb))) e h k H)))).
Qed.



Definition identity_is_Pullback_input {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) : 
 total2 (fun hk : Pb --> Pb => 
   dirprod (hk ;; PullbackPr1 Pb == PullbackPr1 Pb)(hk ;; PullbackPr2 Pb == PullbackPr2 Pb)).
Proof.
  exists (identity Pb).
  apply (dirprodpair).
  apply id_left.
  apply id_left.
Defined.

Lemma PullbackEndo_is_identity {a b c : C}{f : b --> a} {g : c --> a}
   (Pb : Pullback f g) (k : Pb --> Pb) (kH1 : k ;; PullbackPr1 Pb == PullbackPr1 Pb)
                                       (kH2 : k ;; PullbackPr2 Pb == PullbackPr2 Pb) :
       identity Pb == k.
Proof.
  set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (hk ;; _ == _)(hk ;; _ == _))) k (dirprodpair kH1 kH2)).
  assert (H2 : identity_is_Pullback_input Pb == H1).
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 (pr2 (pr2 (pr2 Pb)))).
  apply PullbackSqrCommutes.
(*  set (H:= pr2 (pr2 (pr2 (pr2 Pb)))).  simpl in H.
  set (HH:= H Pb (PullbackPr2 Pb) (PullbackPr1 Pb) (PullbackSqrCommutes Pb)).
  apply HH.
*)
  apply (base_paths _ _ H2).
Qed.
*)

Definition from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : Pb --> Pb'.
Proof.
  apply (PullbackArrow Pb' Pb (PullbackPr2 _ ) (PullbackPr1 _)).
  apply PullbackSqrCommutes.
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




Section Universal_Unique.

Hypothesis H : is_category C.


Lemma isaprop_Pullbacks: isaprop Pullbacks.
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply impred; intro c.
  apply impred; intro f.
  apply impred; intro g.
  apply invproofirrelevance.
  intros Pb Pb'.
  assert (H' : pr1 Pb == pr1 Pb').
  apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))).
  Check (isotoid C H (iso_from_Pullback_to_Pullback Pb Pb')).
  Check (pr2 (pr1 Pb)).
  rewrite transportf_dirprod.
  Check (pr2 (pr1 Pb')).
  Search  ( _ (isotoid _ _ _ ) == _ ).
  rewrite <- (idtoiso_precompose _ _ _ _ (isotoid C H (iso_from_Pullback_to_Pullback Pb Pb'))  ).
  rewrite 
  simpl.
  rewrite transportf_isotoid.
  simpl.
  assert (H' : pr1 (transportf
  (fun x : C =>
   total2
     (fun f' : x --> c =>
      total2
        (fun g' : x --> b =>
         total2 (fun H0 : f';; g == g';; f => isPullback f g f' g' H0))))
  (isotoid C H (iso_from_Pullback_to_Pullback Pb Pb')) (pr2 Pb))  == pr1 (pr2 Pb')).
  destruct Pb as [Pb Pbrest].
  destruct Pb' as [Pb' Pbrest'].
  simpl in *.
  destruct 
  rewrite transport_sigma.
  simpl in *.
  destruct Pbrest as [pro1 Pbrest].
  destruct Pbrest' as [pro1' Pbrest'].
  simpl in *.
  


End Universal_Unique.


End def_pb.
