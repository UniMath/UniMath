Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.AdjunctionHomTypesWeq.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


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







