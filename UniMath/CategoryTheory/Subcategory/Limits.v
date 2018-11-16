(** ** (Co)limits in full subprecategories

If

 * C has (co)limits of shape F,
 * C' : ob C → UU is a proposition on the objects of C, and
 * C' is closed under the formation of (co)limits of shape F,

then the full subcategory on C'-objects has (co)limits of shape F.

Such proofs are mostly just a lot of insertions of

 * [precategory_object_from_sub_precategory_object]
 * [precategory_morphism_from_sub_precategory_morphism]

and their "inverses"

 * [precategory_morphisms_in_subcat]
 * [precategory_object_in_subcat].

Author: Langston Barrett (@siddharthist) (March 2018)

*)

(** ** Contents

- Limits
  - Binary products
- Colimits
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.

Local Open Scope cat.

Section Limits.

(** ** Limits *)

(** *** Terminal objects *)

(** As long as the predicate holds for the terminal object, it's terminal in the full subcategory. *)
Lemma terminal_in_full_subcategory {C : precategory} (C' : hsubtype (ob C))
        (TC : Terminal C) (TC' : C' (TerminalObject TC)) :
  Terminal (full_sub_precategory C').
Proof.
  use tpair.
  - use precategory_object_in_subcat.
    + exact (TerminalObject TC).
    + assumption.
  - cbn.
    intros X.
    use iscontrpair.
    + use morphism_in_full_subcat.
      apply TerminalArrow.
    + intro; apply eq_in_sub_precategory; cbn.
      apply TerminalArrowUnique.
Defined.

(** *** Binary products *)

Lemma bin_products_in_full_subcategory {C : category} (C' : hsubtype (ob C))
      (BPC : BinProducts C)
      (all : ∏ c1 c2 : ob C, C' c1 -> C' c2 -> C' (BinProductObject _ (BPC c1 c2))) :
  BinProducts (full_sub_precategory C').
Proof.
  intros c1' c2'.
  pose (c1'_in_C := (precategory_object_from_sub_precategory_object _ _ c1')).
  pose (c2'_in_C := (precategory_object_from_sub_precategory_object _ _ c2')).
  use tpair; [use tpair|]; [|use dirprodpair|].
  - use precategory_object_in_subcat.
    + apply (BinProductObject _ (BPC c1'_in_C c2'_in_C)).
    + apply all.
      * exact (pr2 c1').
      * exact (pr2 c2').
  - use morphism_in_full_subcat; apply BinProductPr1.
  - use morphism_in_full_subcat; apply BinProductPr2.
  - cbn.
    unfold isBinProduct.
    intros bp' f g.
    use tpair.
    + use tpair.
      * use precategory_morphisms_in_subcat;
          [apply BinProductArrow|exact tt];
          apply (precategory_morphism_from_sub_precategory_morphism _ (full_sub_precategory C'));
          assumption.
      * cbn.
        use dirprodpair; apply eq_in_sub_precategory.
        { apply BinProductPr1Commutes. }
        { apply BinProductPr2Commutes. }
    + intros otherarrow.
      (** This is where we use the condition that C has homsets. *)
      apply subtypeEquality'.
      {
        apply eq_in_sub_precategory.
        cbn.
        apply BinProductArrowUnique.
        - exact (maponpaths pr1 (dirprod_pr1 (pr2 otherarrow))).
        - exact (maponpaths pr1 (dirprod_pr2 (pr2 otherarrow))).
      }
      { apply isapropdirprod;
          apply is_set_sub_precategory_morphisms, homset_property.
      }
Defined.

(** ** Colimits *)

(** *** Initial objects *)

(** As long as the predicate holds for the initial object, it's initial in the full subcategory. *)
Lemma initial_in_full_subcategory {C : precategory} (C' : hsubtype (ob C))
      (IC : Initial C) (IC' : C' (InitialObject IC)) :
  Initial (full_sub_precategory C').
Proof.
  use tpair.
  - use precategory_object_in_subcat.
    + exact (InitialObject IC).
    + assumption.
  - cbn.
    intros X.
    use iscontrpair.
    + use morphism_in_full_subcat.
      apply InitialArrow.
    + intro; apply eq_in_sub_precategory; cbn.
      apply InitialArrowUnique.
Defined.

End Limits.
