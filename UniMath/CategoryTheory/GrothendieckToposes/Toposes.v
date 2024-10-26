(**************************************************************************************************

  Grothendieck toposes

  A Grothendieck topos is a category that is equivalent to the category of sheaves on some site.
  Note that in principle, this is not a proposition, because there are many different sites with the
  same category of sieves. For example, every site with the discrete topology has the same sheaf
  category. Therefore, we need to take the propositional truncation of the site and the equivalence.
  For a univalent Grothendieck topos C, we have an induction principle which shows that a
  proposition holds for C if it holds for all sheaf categories. If we have a 'Grothendieck topos
  structure' (a chosen site and equivalence) for C, we have a recursion principle, which not only
  works for propositions, but for arbitrary type families.

  References
  - Page 127 of 'Sheaves in Geometry and Logic' by Saunders Mac Lane and Ieke Moerdijk.

  Contents
  1. The property of being a Grothendieck topos
    [Grothendieck_topos_structure] [is_Grothendieck_topos]
  2. Grothendieck toposes [Grothendieck_topos]
  3. The recursion and induction principles [Grothendieck_topos_rect] [Grothendieck_topos_ind]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sites.

(** * 1. The property of being a Grothendieck topos *)

Definition Grothendieck_topos_structure
  (C : category)
  : UU
  := ∑ (D : site), adj_equiv C (sheaf_cat D).

Definition Grothendieck_topos_structure_site
  {C : category}
  (G : Grothendieck_topos_structure C)
  : site
  := pr1 G.

Definition Grothendieck_topos_structure_equiv
  {C : category}
  (G : Grothendieck_topos_structure C)
  : adj_equiv C (sheaf_cat (Grothendieck_topos_structure_site G))
  := pr2 G.

Definition is_Grothendieck_topos
  (C : category)
  : hProp
  := ∥ Grothendieck_topos_structure C ∥.

(** * 2. Grothendieck toposes *)

Definition Grothendieck_topos : UU :=
  carrier is_Grothendieck_topos.

Definition make_Grothendieck_topos
  (C : category)
  (G : is_Grothendieck_topos C)
  : Grothendieck_topos
  := C ,, G.

Coercion Grothendieck_topos_category (GT : Grothendieck_topos) : category :=
  pr1 GT.

Definition Grothendieck_topos_is_Grothendieck_topos
  (GT : Grothendieck_topos)
  : is_Grothendieck_topos GT := pr2 GT.

(** * 3. The recursion and induction principles *)

Lemma Grothendieck_topos_rect
  (P : category → UU)
  (HP : ∏ (D : site), P (sheaf_cat D))
  {C : category}
  (HU : is_univalent C)
  (HT : Grothendieck_topos_structure C)
  : P C.
Proof.
  refine (transportf P _ (HP (Grothendieck_topos_structure_site HT))).
  apply (invmap (catiso_is_path_cat _ _)).
  use (adj_equivalence_of_cats_to_cat_iso (adj_equivalence_of_cats_inv _ (Grothendieck_topos_structure_equiv HT))).
  - apply sheaf_cat_univalent.
  - apply HU.
Qed.

Lemma Grothendieck_topos_ind
  (P : category → hProp)
  (HP : ∏ (D : site), P (sheaf_cat D))
  {C : category}
  (HU : is_univalent C)
  (HT : is_Grothendieck_topos C)
  : P C.
Proof.
  revert HT.
  apply hinhuniv.
  exact (Grothendieck_topos_rect P HP HU).
Qed.
