(* -*- coding: utf-8 -*- *)

(* sums (coproducts) *)
Require Import
        UniMath.Foundations.hlevel2.hSet
        UniMath.RezkCompletion.precategories
        UniMath.RezkCompletion.functors_transformations
        UniMath.Ktheory.Utilities.
Require UniMath.Ktheory.Precategories UniMath.Ktheory.Representation UniMath.Ktheory.HomFamily.
Import Ktheory.Utilities.Notation Ktheory.Precategories.Notation.
Definition type (C:precategory) (hs: has_homsets C) {I} (c:I -> ob C) :=
  Representation.Data (HomFamily.precat C hs c).
Definition Object {C:precategory} (hs: has_homsets C) {I} {c:I -> ob C} (r:type C hs c)
           : ob C := Representation.Object r.
Definition In {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C} (B:type C hs b) i :
     Hom (b i) (Object hs B).
Proof. intros. exact (Representation.Element B i). Defined.
Module Coercions.
  Coercion Object : type >-> ob.
End Coercions.
