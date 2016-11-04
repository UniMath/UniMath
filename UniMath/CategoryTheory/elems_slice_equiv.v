Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.equivalences
        UniMath.Ktheory.Elements.

(* Proof that pshf (el P) ≃ (pshf C) / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Definition el {C : Precategory} (P : C ==> SET) : Precategory := cat P.
  Local Definition pshf (C : Precategory) : Precategory := [C^op, SET].

  Variable (C : Precategory).
  Variable (P : pshf C).





End elems_slice_equiv.