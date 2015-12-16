
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of global right Kan extension as right adjoint to precomposition


************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.SubstitutionSystems.AdjunctionHomTypesWeq.
Require Import UniMath.SubstitutionSystems.Notation.


Section RightKanExtension.

Variables C D : precategory.
Variable F : functor C D.
Variable E : precategory.
(* Variable hsC : has_homsets C. *)
Variable hsD : has_homsets D.
Variable hsE : has_homsets E.

Let PrecompWithF : functor _ _
  := pre_composition_functor _ _ E hsD hsE F.

Definition GlobalRightKanExtensionExists : UU
  := is_left_adjoint PrecompWithF.

Definition GlobalRan (H : GlobalRightKanExtensionExists)
  : functor _ _ := right_adjoint H.

End RightKanExtension.
