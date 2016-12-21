
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-  Definition of composition of pointed functors


************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section def_ptd.

Variable C : precategory.
Variable hs : has_homsets C.

Definition ptd_composite (Z Z' : ptd_obj C) : precategory_Ptd C hs.
Proof.
  exists (functor_composite Z Z').
  apply (horcomp (ptd_pt _ Z) (ptd_pt _ Z')).
Defined.

End def_ptd.
