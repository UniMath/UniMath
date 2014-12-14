(* -*- coding: utf-8 -*- *)

Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Sets.
Import Utilities.Notation Precategories.Notation.
Definition set (C:precategory) (hs:has_homsets C) {I} (c:I -> ob C) : ob C -> ob SET.
  intros ? ? ? ? x. 
   apply (Sets.Product (fun i => hSetpair (Hom (c i) x) (hs _ _ ) )).
Defined.
Definition map (C:precategory)(hs: has_homsets C) {I} (c:I -> ob C) (x y:ob C) (f : x → y) :
    set_to_type (set C hs c x) -> set_to_type (set C hs c y).
  intros ? ? ? ? ? ? ? g j; unfold funcomp.
  exact (f ∘ (g j)). Defined.
Definition data (C:precategory) (hs: has_homsets C) {I} (c:I -> ob C)
     : functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
  intros.  exact (set C hs c,, map C hs c). Defined.
Definition precat (C:precategory) (hs: has_homsets C) {I} (c:I -> ob C) : C ==> SET.
  intros. exists (data C hs c). split.
  { intros a. apply funextsec; intros f.  apply funextsec; intros i.
    apply id_right. }
  { intros x y z p q. apply funextsec; intros f. apply funextsec; intros i.
    apply assoc. } Defined.
