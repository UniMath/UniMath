(* -*- coding: utf-8 -*- *)

(* sums (coproducts) *)
Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories.
Require UniMath.Ktheory.HomFamily.

Definition type (C:Precategory) {I} (c:I -> ob C) :=
  Representation (HomFamily.precat C c).

Definition Object {C:Precategory} {I} {c:I -> ob C} (r:type C c)
           : ob C := Object r.

Definition In {C:Precategory} {I} {b:I -> ob C} (B:type C b) i :
     Hom (b i) (Object B).
Proof. intros. exact (Element B i). Defined.

Module Coercions.
  Coercion Object : type >-> ob.
End Coercions.
