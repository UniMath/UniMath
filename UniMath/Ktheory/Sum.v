(* -*- coding: utf-8 -*- *)

(* sums (coproducts) *)
Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Representation Ktheory.HomFamily.
Import Utilities.Notation Precategories.Notation.
Definition type (C:precategory) {I} (c:I -> ob C) :=
  Representation.Data (HomFamily.precat C c).
Definition Object {C:precategory} {I} {c:I -> ob C} (r:type C c)
           : ob C := Representation.Object r.
Definition In {C:precategory} {I} {b:I -> ob C} (B:type C b) i :
     Hom (b i) (Object B).
Proof. intros. exact (Representation.Element B i). Defined.
Module Coercions.
  Coercion Object : type >-> ob.
End Coercions.
