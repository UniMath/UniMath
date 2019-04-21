(** * Colimits in the precategory of types

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

  - Initial object ([InitialType])
  - Binary coproducts ([BinCoproductsType])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.categories.Type.Core.

(** ** Initial object ([InitialType]) *)

(** The [empty] type is an initial object for the precategory of types. *)
Lemma InitialType : Initial type_precat.
Proof.
  apply (mk_Initial (empty : ob type_precat)).
  exact iscontrfunfromempty.
Defined.

(** ** Binary coproducts ([BinCoproductsType]) *)

(** The precategory of types has binary coproducts. *)
Lemma BinCoproductsType : BinCoproducts type_precat.
Proof.
  intros X Y.
  use tpair.
  - exact (coprod X Y,, inl,, inr).
  - apply isBinCoproduct'_to_isBinCoproduct.
    intro Z; apply (weqfunfromcoprodtoprod X Y Z).
Defined.
