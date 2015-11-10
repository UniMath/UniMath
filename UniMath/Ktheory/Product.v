(* -*- coding: utf-8 -*- *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Utilities.
Require UniMath.Ktheory.Representation UniMath.Ktheory.HomFamily.
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
