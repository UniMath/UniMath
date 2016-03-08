(** **********************************************************

Benedikt Ahrens
March 2016


************************************************************)


(** **********************************************************

Contents :

        - special comma categories (c ↓ K)


************************************************************)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


Section const_comma_category_definition.

Variables M C : precategory.
Variable K : functor M C.
Variable c : C.

Definition comma_object :=
  Σ m, C⟦c, K m⟧.

Definition

End comma_category_definition.