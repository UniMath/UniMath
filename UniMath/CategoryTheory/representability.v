Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "C ⟦ a , b ⟧" := (@precategory_morphisms C a b) (at level 2, format "C ⟦ a , b ⟧").
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Section extras.


End extras.

(* The hom functors: Hom(a,_) and Hom(_,b) *)
(* A representable functor is naturally isomorphic to Hom(A,_) *)
(* A representation of a functor F is a pair (A,T) where
   T : Hom(A,_) -> F is a natural isomorphism *)
Section hom_functors.

Variable (C : precategory).
Variable (hsC : has_homsets C).

(* The covariant functor Hom(a,_) *)
Section cov_hom.

Variable a : C.

Definition cov_hom_ob (x : C) : hSet := hSetpair C⟦a,x⟧ (hsC a x).

Definition cov_hom_mor (x y : C) (f : C⟦x,y⟧) :
  cov_hom_ob x -> cov_hom_ob y := fun g => g ;; f.

Definition cov_hom_functor_data : functor_data C HSET :=
  tpair _ _ cov_hom_mor.

Lemma is_functor_cov_hom : is_functor cov_hom_functor_data.
Proof.
split.
  intro f.
  apply funextsec; intro g.
  now apply id_right.
intros b c d f g.
apply funextsec; intro h; simpl.
now apply assoc.
Qed.

Definition cov_hom (c : C) : functor C HSET :=
  tpair _ _ is_functor_cov_hom.

End cov_hom.

(* The contravariant functor Hom(_,b) : C -> Set *)
Section cont_hom.

Variable b : C.

Definition cont_hom_ob (x : C) : hSet := hSetpair C⟦x,b⟧ (hsC x b).

Definition cont_hom_mor (x y : C) (h : C⟦x,y⟧) :
  cont_hom_ob y -> cont_hom_ob x := fun g => h ;; g.

(* Stuck here because only covariant functors in library... Maybe
define this functor as covariant functor on C^op? *)

End cont_hom.
End hom_functors.


(* Contravariant yoneda: C^op -> [C,Set] *)
Variable (C : precategory).
Variable (hsC : has_homsets C).

(* TODO: This is Hom(c,_) *)
Section yoneda_ob.
Variable (c : C^op).

Definition cont_yoneda_objects_ob (d : C) : hSet := hSetpair (C⟦c,d⟧) (hsC c d).

Definition cont_yoneda_objects_mor (d d' : C) (f : C⟦d,d'⟧) :
   cont_yoneda_objects_ob d -> cont_yoneda_objects_ob d' :=
    fun g => g ;; f.

Definition cont_yoneda_ob_functor : functor_data C HSET.
exists cont_yoneda_objects_ob.
exact cont_yoneda_objects_mor.
Defined.

Lemma is_functor_cont_yoneda_ob_functor : is_functor cont_yoneda_ob_functor.
Proof.
split.
  intro f.
  apply funextsec; intro g.
  now apply id_right.
intros a b d f g.
apply funextsec; intro h; simpl.
now apply assoc.
Qed.

Definition cont_yoneda_ob : functor C HSET := 
  tpair _ _ is_functor_cont_yoneda_ob_functor.

End yoneda_ob.

(* Section representability. *)

(* Variables (C : precategory). *)

(* Definition rep (F : functor C HSET) := total2 (fun () => ). *)
