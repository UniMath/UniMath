Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.equivalences.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.AdjunctionHomTypesWeq.

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







