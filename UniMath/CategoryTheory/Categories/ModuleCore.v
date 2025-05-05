(** Authors:
 - Anthony Bordg, March-April 2017
 - Langston Barrett (@siddharthist), November-December 2017 *)

(** * Contents:

- The category of (left) R-modules ([mod_category])
*)

Require Import UniMath.Algebra.AbelianGroups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Categories.AbelianGroup.
Require Import UniMath.CategoryTheory.Actions.

Require Import DisplayedCats.Core.
Require Import DisplayedCats.Constructions.CategoryWithStructure.
Require Import DisplayedCats.Total.

Definition group_endomorphism_ring (G : abgr)
  : ring
  := opposite_ring (endomorphism_ring (C := abgr_PreAdditive) G).

Section Mod.

  Local Open Scope cat.

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
