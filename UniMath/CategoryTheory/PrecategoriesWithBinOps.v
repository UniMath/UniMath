(** ** Precategories with homs having a binary operation *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.


Section def_precategory_with_binops.

  (** Definition of precategories such that homs are binops. *)
  Definition PrecategoryWithBinOpsData (C : precategory) : UU := Π (x y : C), binop (C⟦x, y⟧).

  Definition PrecategoryWithBinOps : UU := Σ C : precategory, PrecategoryWithBinOpsData C.

  Definition PrecategoryWithBinOps_precategory (P : PrecategoryWithBinOps) : precategory := pr1 P.
  Coercion PrecategoryWithBinOps_precategory : PrecategoryWithBinOps >-> precategory.

  Definition mk_PrecategoryWithBinOps (C : precategory) (H : PrecategoryWithBinOpsData C) :
    PrecategoryWithBinOps.
  Proof.
    exact (tpair _ C H).
  Defined.

  (** Gives the binop of the homs from x to y. *)
  Definition to_binop {BC : PrecategoryWithBinOps} (x y : BC) : binop (BC⟦x, y⟧) := (pr2 BC) x y.

End def_precategory_with_binops.
