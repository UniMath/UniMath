(**************************************************************************************************

  Grothendieck toposes

  A Grothendieck topos is a category that is equivalent to the category of sheaves on some site.
  Note that the property of being a Grothendieck topos is not a proposition, because there are many
  different sites with the same category of sieves. For example, every site with the discrete
  topology has the same sheaf category.
  This file defines the data of Grothendieck toposes, together with their constructor and accessors.

  References
  - Page 127 of 'Sheaves in Geometry and Logic' by Saunders Mac Lane and Ieke Moerdijk.

  Contents
  1. Grothendieck toposes [Grothendieck_topos]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sites.

(** * 1. Grothendieck toposes *)

Definition Grothendieck_topos : UU :=
  ∑ (C : category)
    (D : site),
    adj_equiv C (sheaf_cat D).

Definition make_Grothendieck_topos
  (C : category)
  (D : site)
  (F : adj_equiv C (sheaf_cat D))
  : Grothendieck_topos
  := C ,, D ,, F.

Coercion Grothendieck_topos_category (GT : Grothendieck_topos) : category :=
  pr1 GT.

Definition Grothendieck_topos_site
  (GT : Grothendieck_topos)
  : site := pr12 GT.

Definition Grothendieck_topos_equivalence
  (GT : Grothendieck_topos)
  : adj_equiv GT (sheaf_cat (Grothendieck_topos_site GT))
  := pr22 GT.
