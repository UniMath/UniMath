(* -*- coding: utf-8 -*- *)

(* this module is meant to be used without importing it *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Sets.
Local Open Scope cat.

Definition set (C:Precategory) {I} (c:I -> ob C) : ob C -> ob SET.
Proof.
  intros ? ? ? x.
   apply (Sets.Product (fun i => hSetpair (Hom C (c i) x) (homset_property C _ _ ) )).
Defined.

Definition map (C:Precategory) {I} (c:I -> ob C) (x y:ob C) (f : x → y) :
    (set C c x : hSet) -> (set C c y : hSet).
Proof.
  intros ? ? ? ? ? ? g j; unfold funcomp.
  exact (f ∘ (g j)).
Defined.

Definition data (C:Precategory) {I} (c:I -> ob C)
     : functor_data (Precategories.Precategory_obmor C) (Precategories.Precategory_obmor SET).
Proof.
  intros. exact (set C c,, map C c).
Defined.

Definition precat (C:Precategory) {I} (c:I -> ob C) : C ==> SET.
Proof.
  intros. exists (data C c). split.
  { intros a. apply funextsec; intros f.  apply funextsec; intros i.
    apply id_right. }
  { intros x y z p q. apply funextsec; intros f. apply funextsec; intros i.
    apply assoc. }
Defined.
