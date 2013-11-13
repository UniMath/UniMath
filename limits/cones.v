Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section Cone.

Variables J C : precategory.

Variable F : functor J C.

Definition ConeData := total2 (
  fun a : C => forall j : J, a --> F j).

Definition ConeTop (a : ConeData) : C := pr1 a.
Definition ConeMor (a : ConeData) (j : J) : ConeTop a --> F j := (pr2 a) j.

Definition ConeProp (a : ConeData) :=
  forall j j' (f : j --> j'), ConeMor a j ;; #F f == ConeMor a j'.

Definition Cone := total2 (fun a : ConeData => ConeProp a).

Definition ConeData_from_Cone : Cone -> ConeData := fun a => pr1 a.
Coercion ConeData_from_Cone : Cone >-> ConeData.

Definition ConeProp_from_Cone (a : Cone) : ConeProp a := pr2 a.
Coercion ConeProp_from_Cone : Cone >-> ConeProp.


Lemma cone_prop (a : Cone) : 
  forall j j' (f : j --> j'), ConeMor a j ;; #F f == ConeMor a j'.
Proof.
  exact (pr2 a).
Qed.


Definition Cone_Mor (M N : Cone) := 
  total2 (fun f : ConeTop M --> ConeTop N =>
        forall j : J, f ;; ConeMor N j == ConeMor M j).


Lemma isaset_Cone_Mor (M N : Cone) : isaset (Cone_Mor M N).
Proof.
  apply (isofhleveltotal2 2).
  apply (pr2 (_ --> _ )).
  intros.
  apply hlevelntosn.
  apply impred.
  intros.
  apply (pr2 (_ --> _ )).
Qed.

Definition ConeConnect {M N : Cone} (f : Cone_Mor M N) : 
    ConeTop M --> ConeTop N := pr1 f.

Lemma Cone_Mor_eq (M N : Cone) (f g : Cone_Mor M N) : 
   ConeConnect f == ConeConnect g -> f == g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply impred; intro; apply (pr2 (_ --> _)).
Qed.

Lemma cone_mor_prop M N (f : Cone_Mor M N) : 
    forall j : J, ConeConnect f ;; ConeMor N j == ConeMor M j.
Proof.
  exact (pr2 f).
Qed.

Definition Cone_id (A : Cone) : Cone_Mor A A.
Proof.
  exists (identity _).
  intros; apply id_left.
Defined.


Definition Cone_comp (A B D : Cone) (f : Cone_Mor A B)
        (g : Cone_Mor B D) : Cone_Mor A D.
Proof.
  exists (ConeConnect f ;; ConeConnect g).
  intro j.
  (* make this proof opaque *)
  rewrite <- assoc.
  rewrite cone_mor_prop.
  rewrite cone_mor_prop.
  apply idpath.
Defined.
Check is_precategory.
Print precategory_data.


Definition Cone_precategory_ob_mor : precategory_ob_mor := 
   precategory_ob_mor_pair Cone 
   (fun a b => hSetpair (Cone_Mor a b) (isaset_Cone_Mor a b)).

Definition Cone_precategory_data : precategory_data.
Proof.
  exists Cone_precategory_ob_mor.
  exists Cone_id.
  exact Cone_comp.
Defined.

Lemma is_precategory_Cone : is_precategory Cone_precategory_data.
Proof.
  repeat split; simpl.
  
  intros;
  apply Cone_Mor_eq;
  simpl; apply id_left.
  
  intros;
  apply Cone_Mor_eq;
  simpl; apply id_right.
  
  intros; 
  apply Cone_Mor_eq;
  simpl; apply assoc.
Qed.
  
Definition CONE : precategory := tpair _ _ is_precategory_Cone.  

Program Instance CONE_struct : Cat_struct Cone_Hom := {
  mor_oid := Cone_Hom_oid;
  id := Cone_id;
  comp := Cone_comp
}.
Next Obligation.
Proof.
  unfold Proper; 
  do 2 red.
  simpl.
  intros x y H x' y' H'.
  rewrite H, H'.
  cat.
Qed.

Definition CONE := Build_Cat CONE_struct.

End Cone.

(** a limit is a terminal object in (CONE A) *)



Definition LIMIT A := Terminal (CONE A).

(** easy access to interesting parts of a limit *)

Section Limit_defs.

Variable A : Functor J C.

Hypothesis H : LIMIT A.

Definition Limit : Cone A := Term (Terminal := H).

Definition LimitVertex : obC := ConeTop Limit.

Definition LimitMor (j : obJ) := cone_mor (ConeClass := Limit) j.

End Limit_defs.

End defs.