(* -*- coding: utf-8 -*- *)

Require Import Ktheory.Utilities.
Require Import RezkCompletion.precategories 
               RezkCompletion.yoneda
               RezkCompletion.category_hset
               RezkCompletion.functors_transformations
               .
Require Import Foundations.hlevel2.hSet.
Import Ktheory.Utilities.Notation.
Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := tpair _ C i.
Module Precategory.
  Definition obmor (C:precategory) : precategory_ob_mor := 
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C).
  Definition obj (C:precategory) : Type :=
    ob (
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C)).
  Definition mor {C:precategory} : ob C -> ob C -> UU :=
    pr2 (
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C)).
End Precategory.
Module Functor.
  Definition obmor {C D} (F:functor C D) := pr1 F.
  Definition obj {C D} (F:functor C D) := pr1 (pr1 F).
  Definition mor {C D} (F:functor C D) := pr2 (pr1 F).
  Definition identity {C D} (F:functor C D) := functor_id F.
  Definition compose {C D} (F:functor C D) := functor_comp F.
End Functor.
Module Import Notation.
  Notation Hom := Precategory.mor.
  Notation "b ← a" := (precategory_morphisms a b) (at level 50).
  Notation "a → b" := (precategory_morphisms a b) (at level 50).
  Notation "a ==> b" := (functor a b) (at level 50).
  Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing).
  Notation "g ∘ f" := (precategories.compose f g) (at level 50, only parsing).
  Notation "# F" := (functor_on_morphisms F) (at level 3).
  Notation "C '^op'" := (opp_precat C) (at level 3).
  Notation SET := hset_precategory.
End Notation.

Definition category_pair (C:precategory) (i:is_category C)
 : category := tpair _ C i.

Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

Definition reflects_isos {C D} (X:C==>D) :=
  forall c c' (f : c → c'), is_isomorphism (#X f) -> is_isomorphism f.

Lemma isaprop_reflects_isos {C D} (X:C==>D) : isaprop (reflects_isos X).
Proof.
  intros. apply impred; intros. apply impred; intros. apply impred; intros.
  apply impred; intros. apply isaprop_is_isomorphism. Qed.

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU)
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => mor i j)).
Defined.    

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (* identity : forall i, mor i i) *)
    (compose : forall i j k (f:mor i j) (g:mor j k), mor i k)
    : precategory_data.
  intros.
  exact (tpair _  (makePrecategory_ob_mor obj mor) compose).
Defined.    

Definition makePrecategory 
    (obj : UU)
    (mor : obj -> obj -> UU)
    (identity : forall i, mor i i)
    (compose : forall i j k (f:mor i j) (g:mor j k), mor i k)
    (right : forall i j (f:mor i j), compose _ _ _ (identity i) f = f)
    (left  : forall i j (f:mor i j), compose _ _ _ f (identity j) = f)
    (associativity : forall a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) = compose _ _ _ (compose _ _ _ f g) h)
    : precategory.
  intros.
  apply (precategory_pair 
           (makePrecategory_data obj mor compose)).
  split.
  - exists identity; split.
    + exact right.
    + exact left.
  - exact associativity.
Defined.    

Lemma has_homsets_opp_precat (C: precategory) (hs: has_homsets C) : has_homsets (C^op).
Proof.
  intros C hs a b.
  apply hs.
Qed.

(** *** opposite category of opposite category *)

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C = opp_precat_ob_mor (opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.
(*
Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ = maponpaths precategory_comp (opp_opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.
*)
Lemma opp_opp_precat_data (C : precategory_data) 
   : C = opp_precat_data (opp_precat_data C).
Proof. intros [[ob mor] co]. reflexivity. Defined.

Lemma has_homsets_opp_precat_data (C : precategory_data)(hs : has_homsets C) : 
  has_homsets (opp_precat_data (opp_precat_data C)).
Proof.
  intros C hs a b.
  apply hs.
Qed.  

Lemma opp_opp_precat (C : precategory)(hsC: has_homsets (pr1 C)) : C = C^op^op.
Proof. intros [data ispre] hsC.
       apply (total2_paths2_second_isaprop (opp_opp_precat_data data)).
       apply isaprop_is_precategory.
       apply has_homsets_opp_precat_data. 
       apply hsC.
Defined.
