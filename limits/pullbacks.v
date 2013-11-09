
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section def_pb.

Variable C : precategory.


Definition isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (f' : d --> c) (g' : d --> b) (H : f' ;; g == g';; f) : UU :=
   forall e (h : e --> b) (k : e --> c)(H : k ;; g == h ;; f ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk ;; f' == k)(hk ;; g' == h))).

Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun p =>
     total2 (fun f' : p --> c =>
     total2 (fun g' : p --> b =>
     total2 (fun H : f' ;; g == g' ;; f =>
        isPullback f g f' g' H)))).

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

Definition helper {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) : 
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
  assert (H2 : helper Pb == H1).
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

Definition isInitial (a : C) := forall b : C, iscontr (a --> b).

Definition Initial := total2 (fun a => isInitial a).

Definition InitialObject (O : Initial) : C := pr1 O.
Coercion InitialObject : Initial >-> ob.

Definition InitialArrow (O : Initial) (b : C) : O --> b :=  pr1 (pr2 O b).

Lemma InitialEndo_is_identity (O : Initial) (f : O --> O) : identity O == f.
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 O O).
Qed.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) : 
   is_isomorphism (InitialArrow O O').
Proof.
  exists (InitialArrow O' O).
  split; apply pathsinv0;
   apply InitialEndo_is_identity.
Qed.

Definition hasInitial := ishinh Initial.



(*
Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun dfg : total2 (fun d : C => dirprod (d --> c) (d --> b)) =>
     total2 (fun H : pr1 (pr2 dfg) ;; g == pr2 (pr2 dfg) ;; f =>       
           isPullback f g (pr1(pr2 dfg)) (pr2 (pr2 dfg)) H )).
*)


Section Universal_Unique.

Hypothesis H : is_category C.

(*

Lemma isaset_Initial : isaset Initial.
Proof.
  apply isofhlevelonestep.
  intros x y.
  fold isaprop.
  simpl.

*)

Lemma isaprop_Initial : isaprop Initial.
Proof.
  apply invproofirrelevance.
  intros a a'.
  apply total2_paths.

End Initial_Unique.




(*
Definition pb_corner {a b c : C} {f : b --> a} {g : c --> a}: 
   pullback f g -> C := fun H => pr1 (pr1 H).
*)

(*
Definition pb_pr1 {a b c : ob C} {f : b --> a} {g : c --> a}
   (P : pullback f g) : pb_corner P --> b := pr2 (pr2 (pr1 P)).

Definition pb_pr2 {a b c : ob C} {f : b --> a} {g : c --> a}
   (P : pullback f g) : pb_corner P --> c := pr1 (pr2 (pr1 P)).

Definition pb_square_comm {a b c : ob C}{f : b --> a} {g : c --> a}
   (P : pullback f g) : pb_pr1 P ;; f == pb_pr2 P ;; g.
Proof.
  apply pathsinv0.
  apply (pr1 (pr2 P)).
Qed.

(* TODO: opacify it by defining it by tactics *)
Definition arrow_to_pb_corner {a b c : ob C} (f : b --> a) (g : c --> a) 
  (P : pullback f g) e (h : e --> b) (k : e --> c) (H : h ;; f == k ;; g) :
        e --> pb_corner P := 
     pr1 (pr1 (pr2 (pr2 P) e h k H)).

Definition from_pb_to_pb {a b c : ob C}(f : b --> a) (g : c --> a)
  (P P' : pullback f g) : pb_corner P --> pb_corner P' :=
  arrow_to_pb_corner f g P' (pb_corner P) 
  (pb_pr1 P) (pb_pr2 P).
  (pr1 (pr2 P _ _ _ _ )).
   
*)

End def_pb.