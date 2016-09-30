(** * Additive categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** * Definition of additive categories *)
Section def_additive.

  (** A preadditive category is additive if it has a zero object and binary
    direct sums. *)
  Definition isAdditive (PA : PreAdditive) : UU := (Zero PA) × (BinDirectSums PA).

  Definition mk_isAdditive (PA : PreAdditive) (H1 : Zero PA) (H2 : BinDirectSums PA) :
    isAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  (** Definition of additive categories *)
  Definition Additive : UU := Σ PA : PreAdditive, isAdditive PA.

  Definition Additive_PreAdditive (A : Additive) : PreAdditive := pr1 A.
  Coercion Additive_PreAdditive : Additive >-> PreAdditive.

  Definition mk_Additive (PA : PreAdditive) (H : isAdditive PA) : Additive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  (** Accessor functions. *)
  Definition to_isAdditive (A : Additive) : isAdditive A := pr2 A.

  Definition to_Zero (A : Additive) : Zero A := dirprod_pr1 (to_isAdditive A).

  Definition to_BinDirectSums (A : Additive) : BinDirectSums A := dirprod_pr2 (to_isAdditive A).

End def_additive.
