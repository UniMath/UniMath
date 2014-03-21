(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Sets.
Import Utilities.Notation Precategories.Notation.
Definition set (C:precategory) {I} (c:I -> ob C) : ob C -> ob SET.
  intros ? ? ? x. exact (Sets.Product (fun i => Hom (c i) x)). Defined.
Definition map (C:precategory) {I} (c:I -> ob C) (x y:ob C) (f : x → y) :
    set_to_type (HomFamily.set C c x) -> set_to_type (HomFamily.set C c y).
  intros ? ? ? ? ? ? g j; unfold funcomp.
  exact (f ∘ (g j)). Defined.
Definition data (C:precategory) {I} (c:I -> ob C)
     : functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
  intros.  exact (HomFamily.set C c,, HomFamily.map C c). Defined.
Definition precat (C:precategory) {I} (c:I -> ob C) : C ==> SET.
  intros. exists (HomFamily.data C c). split.
  { intros a. apply funextsec; intros f.  apply funextsec; intros i.
    apply id_right. }
  { intros x y z p q. apply funextsec; intros f. apply funextsec; intros i.
    apply assoc. } Defined.
