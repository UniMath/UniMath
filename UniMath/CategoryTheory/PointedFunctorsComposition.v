
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-  Definition of composition of pointed functors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Section def_ptd.

Variable C : precategory.
Variable hs : has_homsets C.

Definition ptd_composite (Z Z' : ptd_obj C) : precategory_Ptd C hs.
Proof.
  exists (functor_composite Z Z').
  apply (horcomp (ptd_pt _ Z) (ptd_pt _ Z')).
Defined.

End def_ptd.
