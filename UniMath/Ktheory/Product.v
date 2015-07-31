(* -*- coding: utf-8 -*- *)

Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Representation Ktheory.HomFamily.
Import Ktheory.Utilities.Notation Ktheory.Precategories.Notation.
Definition type (C:precategory) (hs: has_homsets C) {I} (c:I -> ob C) :=
  Representation.Data (HomFamily.precat C^op (Precategories.has_homsets_opp_precat C hs) c).
Definition Object {C:precategory} (hs: has_homsets C) {I} {c:I -> ob C} (r:type C hs c)
           (* the representing object of r is in C^op, so here we convert it *)
           : ob C := Representation.Object r.
Definition Proj {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C} (B:type C hs b) i : 
  Hom (Object hs B) (b i).
Proof. intros. exact (Representation.Element B i). Defined.
Module Coercions.
  Coercion Object : type >-> ob.
End Coercions.
