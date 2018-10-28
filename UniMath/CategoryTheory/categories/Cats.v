(** * The (pre)category of (pre)categories

This file defines the (pre)category of 𝒰-small (pre)categories, i.e.
(pre)categories that fit within some fixed universe.

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

- The precategory of 𝒰-small precategories (for fixed U) ([precat_precat])
- The precategory of 𝒰-small categories (for fixed U) ([cat_precat])
- (Co)limits
  - Colimits
  - Limits
    - Terminal precategory ([TerminalPrecat])
    - Terminal category ([TerminalCat])
    - Products ([ProductsCat])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

(* (Co)limits *)
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.
Local Open Scope functions.

(** ** The precategory of 𝒰-small precategories (for fixed U) ([precat_precat]) *)

Definition precat_precat : precategory.
Proof.
  use mk_precategory_one_assoc.
  - use tpair; use tpair; cbn.
    + exact precategory.
    + exact functor.
    + exact functor_identity.
    + exact @functor_composite.
  - repeat split; intros.
    + apply functor_identity_right.
    + apply pathsinv0, functor_assoc.
Defined.

(** ** The precategory of 𝒰-small categories (for fixed U) ([cat_precat]) *)

Definition cat_precat : precategory.
Proof.
  use mk_precategory_one_assoc.
  - use tpair; use tpair; cbn.
    + exact category.
    + exact functor.
    + exact functor_identity.
    + exact @functor_composite.
  - repeat split; intros.
    + apply functor_identity_right.
    + apply pathsinv0, functor_assoc.
Defined.

(** ** (Co)limits *)

(** *** Colimits *)

(** **** Initial category ([InitialCat]) *)

(** *** Limits *)

(** **** Terminal precategory ([TerminalPrecat]) *)

Definition TerminalPrecat : Terminal precat_precat.
Proof.
  use mk_Terminal.
  - cbn; exact unit_category.
  - intros ?; apply iscontr_functor_to_unit.
Defined.

(** **** Terminal category ([TerminalCat]) *)

Definition TerminalCat : Terminal cat_precat.
Proof.
  use mk_Terminal.
  - cbn; exact unit_category.
  - intros ?; apply iscontr_functor_to_unit.
Defined.

(** **** Products ([ProductsCat]) *)

(** We essentially proved the universal property in [functor_into_product_weq],
    an equivalence between A → (product_category B) and (∏ i : I, A → (B i)).
  *)
Definition ProductsCat {I : UU} : Products I cat_precat.
Proof.
  intros f; cbn in *.
  use mk_Product.
  - exact (product_category f).
  - intro i; exact (pr_functor I f i).
  - intros other_prod other_proj; cbn in other_proj.
    apply (@iscontrweqf (hfiber functor_into_product_weq other_proj)).
    + use weqfibtototal; intros other_functor; cbn.
      use weqpair.
      * apply toforallpaths.
      * apply isweqtoforallpaths.
    + apply weqproperty.
Defined.

(** *)
