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



Section Cone_Homs.

Variables M N : Cone.




Class Cone_Hom_struct (f : morC M N) := {
  cone_comm : forall j:obJ, f ;; cone_mor j == cone_mor j 
}.

Record Cone_Hom := {
  cone_hom_carrier :> morC M N;
  cone_hom_struct :> Cone_Hom_struct cone_hom_carrier
}.

Lemma Cone_Hom_equiv : @Equivalence Cone_Hom 
         (fun A B => cone_hom_carrier A == cone_hom_carrier B).
Proof.
  split.
  unfold Reflexive;
  cat.
  unfold Symmetric;
  intros x y; 
  apply hom_sym.
  unfold Transitive;
  intros x y z;
  apply hom_trans.
Qed.

Definition Cone_Hom_oid := Build_Setoid Cone_Hom_equiv.

End Cone_Homs.

Existing Instance cone_hom_struct.

Section Cone_id_comp.

Variable A : Cone.

Program Definition Cone_id : Cone_Hom A A := 
   Build_Cone_Hom (cone_hom_carrier := id _ ) _ .
Next Obligation.
Proof.
  constructor.
  cat.
Qed.

Variables B D : Cone.
Variable f : Cone_Hom A B.
Variable g : Cone_Hom B D.

Program Definition Cone_comp : Cone_Hom A D := 
    Build_Cone_Hom (cone_hom_carrier := cone_hom_carrier f ;; 
                                        cone_hom_carrier g) _ .
Next Obligation.
Proof.
  constructor.
  intro j.
  rewrite assoc.
  rewrite (cone_comm j).
  rewrite (cone_comm j).
  cat.
Qed.

End Cone_id_comp.

Obligation Tactic := cat ; try apply assoc.

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