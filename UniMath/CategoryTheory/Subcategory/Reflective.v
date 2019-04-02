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

  Context {C : precategory}.

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

End Def.

Arguments reflective_subcategory _ : clear implicits.