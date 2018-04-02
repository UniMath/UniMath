(** * The category of finite sets

Author: Langston Barrett (@siddharthist)

*)


(** ** Contents:

- The univalent category [FinSet] of finite sets/types
- (Co)limits
  - Colimits
  - Limits
    - Binary products

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Combinatorics.FiniteSets.

(* Basics *)
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

(* HSET *)
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

(* Lemmas about forming (full) subcategories *)
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

(* Limits *)
Require Import UniMath.CategoryTheory.Subcategory.Limits.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.
Local Open Scope functions.

(** ** The univalent category [FinSet] of finite sets/types *)

(** This could be defined in three ways:
    1. as a subcategory of [type_precat],
    2. as a subcategory of [HSET] (see [isfinite_isaset]), or
    3. as a regular precategory.

    We choose the second due to the ability to inherit many structures from [HSET].
 *)
Definition finite_subtype : hsubtype (ob HSET) := isfinite ∘ pr1hSet.
Definition FinSet : univalent_category :=
  subcategory_univalent HSET_univalent_category finite_subtype.

(** ** (Co)limits *)

(** *** Colimits *)

(** *** Limits *)

(** The product of finite sets is finite, so the predicate "is finite" is closed
    under the formation of products. Therefore, FinSet inherits products from HSET. *)
Definition BinProductsFinSet : BinProducts FinSet.
Proof.
  apply (@bin_products_in_full_subcategory HSET_univalent_category
                                           finite_subtype BinProductsHSET).
  intros; apply isfinitedirprod; assumption.
Defined.
