(** ** Precategories such that spaces of morphisms have a binary operation *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.


Section def_precategory_with_binops.

  (** Definition of precategories such that homs are binops. *)
  Definition precategoryWithBinOpsData (C : precategory) : UU := Π (x y : C), binop (C⟦x, y⟧).

  Definition precategoryWithBinOps : UU := Σ C : precategory, precategoryWithBinOpsData C.

  Definition precategoryWithBinOps_precategory (P : precategoryWithBinOps) : precategory := pr1 P.
  Coercion precategoryWithBinOps_precategory : precategoryWithBinOps >-> precategory.

  Definition mk_precategoryWithBinOps (C : precategory) (H : precategoryWithBinOpsData C) :
    precategoryWithBinOps := tpair _ C H.

  (** Gives the binop of the homs from x to y. *)
  Definition to_binop {BC : precategoryWithBinOps} (x y : BC) : binop (BC⟦x, y⟧) := (pr2 BC) x y.

End def_precategory_with_binops.
