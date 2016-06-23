(** precategories such that homs have binops. *)
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
  Definition is_PrecategoryWithBinOps (C : precategory) :=
    forall (x y : C), binop (C⟦x, y⟧).
  Definition mk_isPrecategoryWithBinOps (C : precategory)
             (H : forall (x y : C), binop(C⟦x, y⟧)) :
    is_PrecategoryWithBinOps C.
  Proof.
    intros x y.
    exact (H x y).
  Defined.

  Definition PrecategoryWithBinOps :
    UU := Σ C : precategory, is_PrecategoryWithBinOps C.
  Definition PrecategoryWithBinOps_precategory (P : PrecategoryWithBinOps) :
    precategory := pr1 P.
  Coercion PrecategoryWithBinOps_precategory :
    PrecategoryWithBinOps >-> precategory.

  Variable BC : PrecategoryWithBinOps.

  Definition mk_PrecategoryWithBinOps (C : precategory)
             (H : is_PrecategoryWithBinOps C) : PrecategoryWithBinOps.
  Proof.
    exact (tpair _ C H).
  Defined.

  (** Gives the binop of the homs from x to y. *)
  Definition PrecategoryWithBinOps_binop (x y : BC) :
    binop (BC⟦x, y⟧) := (pr2 BC) x y.

End def_precategory_with_binops.
