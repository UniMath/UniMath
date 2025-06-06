(**

  The Category of R-Modules

  This file defines the category of ring modules for a fixed ring R via a displayed category over
  the category of abelian groups. The data over a group G are the ring morphisms from R to the
  (opposite) endomorphism ring of G.

  Contents
  1. The category of R-modules [module_category]

  Originally written by Anthony Bordg, Langston Barrett (@siddharthist)

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.AbelianGroups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Actions.
Require Import UniMath.CategoryTheory.Categories.AbelianGroup.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.CategoryWithStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

(** * 1. The category of R-modules *)

Definition group_endomorphism_ring (G : abgr)
  : ring
  := opposite_ring (endomorphism_ring (C := abgr_PreAdditive) G).

Section Mod.

  Context (R : ring).

  Definition module_disp_cat : disp_cat abelian_group_category.
  Proof.
    use disp_struct.
    - intro M.
      exact (ringfun R (group_endomorphism_ring M)).
    - intros M N f g h.
      exact (∏ r, f r · h = h · g r).
    - abstract (
        intros;
        apply impred_isaprop;
        intro;
        apply homset_property
      ).
    - abstract (
        intros M f r;
        exact (id_right _ @ !id_left _)
      ).
    - abstract (
        intros L M N f g h s t Hs Ht r;
        now rewrite assoc, Hs, assoc', Ht, assoc
      ).
  Defined.

  Definition module_category : category := total_category module_disp_cat.

End Mod.
