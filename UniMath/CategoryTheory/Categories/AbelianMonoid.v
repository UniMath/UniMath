(**

  The Univalent Category of Abelian Monoids

  This file shows that the category of abelian monoids, already defined in Magma.v, is univalent.

  Contents
  1. The univalent category of abelian monoids [abelian_monoid_univalent_category]

 *)
Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The univalent category of abelian monoids *)

Definition is_univalent_abelian_monoid_disp_cat
  : is_univalent_disp abelian_monoid_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_monoid_disp_cat
    is_univalent_abelian_magma_disp_cat.

Definition is_univalent_abelian_monoid_category
  : is_univalent abelian_monoid_category
  := is_univalent_total_category
    is_univalent_magma_category
    is_univalent_abelian_monoid_disp_cat.

Definition abelian_monoid_univalent_category : univalent_category :=
  make_univalent_category abelian_monoid_category is_univalent_abelian_monoid_category.
