(** * The (pre)category of (pre)categories

This file defines the (pre)category of 𝒰-small (pre)categories, i.e.
(pre)categories that fit within some fixed universe.

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

- Definitions
  - The precategory of 𝒰-small precategories (for fixed U) ([precat_precat])
  - The precategory of 𝒰-small categories ([cat_precat])
  - The precategory of 𝒰-small univalent categories ([univalent_cat_precat])
  - The category of 𝒰-small set categories ([setcat_cat])
- Colimits
  - Initial objects
    - Initial precategory ([InitialPrecat])
    - Initial category ([InitialCat])
    - Initial univalent category ([InitialUniCat])
- Limits
  - Terminal objects
    - Terminal precategory ([TerminalPrecat])
    - Terminal category ([TerminalCat])
    - Terminal univalent category ([TerminalUniCat])
    - Terminal setcategory ([TerminalSetCat])
  - Products
    - Product category ([ProductsCat])
  - Notes on equalizers
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.catiso.

(* Subcategories *)
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.Limits.

(* (Co)limits *)
Require Import UniMath.CategoryTheory.categories.StandardCategories. (* unit *)
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.
Local Open Scope functions.

(** ** Definitions *)

(** *** The precategory of 𝒰-small precategories (for fixed 𝒰) ([precat_precat]) *)

Definition precat_precat : precategory.
Proof.
  use make_precategory_one_assoc.
  - use tpair; use tpair; cbn.
    + exact precategory.
    + exact functor.
    + exact functor_identity.
    + exact @functor_composite.
  - repeat split; intros.
    + apply functor_identity_right.
    + apply pathsinv0, functor_assoc.
Defined.

(** *** The precategory of 𝒰-small categories ([cat_precat]) *)

Definition cat_precat_subtype : hsubtype precat_precat :=
  λ C : precategory, make_hProp _ (isaprop_has_homsets C).

(** This can also be seen as a subcategory of [cat_precat].
    An isommorphism between them would be useful because it is easier to prove
    e.g. that [cat_precat] has products, and then inherit them in
    [univalent_cat_precat]. *)


(** Two copies of a proposition are as good as one.
    This is like the structural rule of contraction. *)
Local Lemma dirprod_with_prop (A : UU) (isa : isaprop A) : A × A ≃ A.
Proof.
  apply weqpr1, iscontraprop1; assumption.
Defined.

(** A variation on the above theme *)
Local Lemma dirprod_with_prop' (A B : UU) (isa : isaprop A) : A × B × A ≃ B × A.
Proof.
  intermediate_weq ((A × B) × A).
  apply invweq, weqtotal2asstor.
  intermediate_weq (A × (A × B)).
  apply weqdirprodcomm.
  intermediate_weq ((A × A) × B).
  apply invweq, weqtotal2asstor.
  intermediate_weq (A × B).
  apply weqdirprodf.
  - apply dirprod_with_prop; assumption.
  - apply idweq.
  - apply weqdirprodcomm.
Defined.
