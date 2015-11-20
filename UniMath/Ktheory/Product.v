(* -*- coding: utf-8 -*- *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Utilities.
Local Open Scope cat.
Require UniMath.Ktheory.HomFamily.

Definition type (C:Precategory) {I} (c:I -> ob C) :=
  Representation (HomFamily.precat C^op c).

Definition Object {C:Precategory} {I} {c:I -> ob C} (r:type C c)
           (* the representing object of r is in C^op, so here we convert it *)
           : ob C := universalObject r.

Definition Proj {C:Precategory} {I} {b:I -> ob C} (B:type C b) i :
  Hom C (Object B) (b i).
Proof. intros. exact (universalElement B i). Defined.

Module Coercions.
  Coercion Object : type >-> ob.
End Coercions.
