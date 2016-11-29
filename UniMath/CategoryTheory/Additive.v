(** * Additive categories. *)
(** * Contents
- Definition of additive categories
- Quotient of an additive category is additive
*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** * Definition of additive categories *)
Section def_additive.

  (** A preadditive category is additive if it has a zero object and binary direct sums. *)
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

  Definition to_BinCoproducts (A : Additive) : BinCoproducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinCoproduct A (to_BinDirectSums A X Y)).
  Defined.

  Definition to_BinProducts (A : Additive) : BinProducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinProduct A (to_BinDirectSums A X Y)).
  Defined.

End def_additive.


(** * Quotient is additive
    We show that quotient of an additive category by certain subgroups is additive. In particular,
    this is used to show that the naive homotopy category of the category of chain complexes is an
    Additive precategory. *)
Section additive_quot_additive.

  Variable A : Additive.
  Hypothesis PAS : PreAdditiveSubabgrs A.
  Hypothesis PAC : PreAdditiveComps A PAS.

  Definition QuotPrecategory_Additive : Additive.
  Proof.
    use mk_Additive.
    - exact (QuotPrecategory_PreAdditive A PAS PAC).
    - use mk_isAdditive.
      + exact (QuotPrecategory_Zero A PAS PAC (to_Zero A)).
      + exact (QuotPrecategory_BinDirectSums A (to_BinDirectSums A) PAS PAC).
  Defined.

End additive_quot_additive.
