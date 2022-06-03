(** * Reflective subcategories *)
(** ** Contents

  - Definition
 *)

Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Section Def.

  Context {C : category}.

  Definition is_reflective (D : hsubtype C) :=
    is_right_adjoint (sub_precategory_inclusion C (full_sub_precategory D)).

  Definition reflective_subcategory : UU :=
    ∑ D : hsubtype C, is_reflective D.

  Definition reflective_subcategory_to_hsubtype
            (D : reflective_subcategory) : hsubtype C :=
    pr1 D.

  Coercion reflective_subcategory_to_hsubtype :
    reflective_subcategory >-> hsubtype.

  Definition reflective_subcategory_to_precategory :
    reflective_subcategory -> precategory.
    intro D; exact (full_sub_precategory D).
  Defined.

  Coercion reflective_subcategory_to_precategory :
    reflective_subcategory >-> precategory.

  Definition localization (R : reflective_subcategory) :
    functor C (full_sub_precategory R) := left_adjoint (pr2 R).

End Def.

Arguments reflective_subcategory _ : clear implicits.

Lemma localization_is_idempotent {C : category} (R : reflective_subcategory C)
      (d : ob R) :
  z_iso (localization R (precategory_object_from_sub_precategory_object _ _ d)) d.
Proof.
  exists ((counit_from_left_adjoint (pr2 (pr2 R))) d).
  abstract (
        apply (@counit_is_z_iso_if_right_adjoint_is_fully_faithful
                 C (subcategory C (full_sub_precategory R)) _ _ (pr2 (pr2 R))),
        fully_faithful_sub_precategory_inclusion).
Defined.
