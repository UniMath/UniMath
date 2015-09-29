Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "'hom' C" := (@precategory_morphisms C) (at level 2).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Section yoneda.

Lemma has_homsets_HSET : has_homsets HSET.
Proof. intros a b; apply isaset_set_fun_space. Qed.

(* Contravariant yoneda: C^op -> [C,Set] *)
Variable (C : precategory).
Variable (hsC : has_homsets C).

(* TODO: This is Hom(c,_) *)
Section yoneda_ob.
Variable (c : C^op).

Definition cont_yoneda_objects_ob (d : C) : hSet := hSetpair (hom C c d) (hsC c d).

Definition cont_yoneda_objects_mor (d d' : C) (f : hom C d d') :
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

End yoneda.

(* Section representability. *)

(* Variables (C : precategory). *)

(* Definition rep (F : functor C HSET) := total2 (fun () => ). *)

