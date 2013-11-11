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

Section epis_and_monos.

Variable C : precategory.


Definition is_epi {a b : C} (f : a --> b) :=
   forall e (g h : b --> e), f;;g == f;;h -> g == h.

Lemma isaprop_is_epi (a b : C) (f : a --> b) : isaprop (is_epi f).
Proof.
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.

Definition epi (a b : C) := total2 (fun f : a --> b => is_epi f).

Definition morphism_from_epi (a b : C) : epi a b -> a --> b := fun f => pr1 f.
Coercion morphism_from_epi : epi >-> pr1hSet.



Definition is_mono {a b : C} (f : a --> b) :=
   forall e (g h : e --> a), g;;f == h;;f -> g == h.

Lemma isaprop_is_mono (a b : C) (f : a --> b) : isaprop (is_mono f).
Proof.
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.

Definition mono (a b : C) := total2 (fun f : a --> b => is_mono f).

Definition morphism_from_mono (a b : C) : mono a b -> a --> b := fun f => pr1 f.
Coercion morphism_from_mono : mono >-> pr1hSet.

(* insert lemmas about equalities of epis and monos *)

End epis_and_monos.


(* stuff about split monos and split epis? *)