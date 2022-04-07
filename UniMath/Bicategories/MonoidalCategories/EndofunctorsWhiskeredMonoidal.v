(** **********************************************************

Ralph Matthes

2022, after the model of EndofunctorsMonoidal
*)

(** **********************************************************

Contents :

- build monoidal category for the endofunctors

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.


Local Open Scope cat.

Section Endofunctors_as_monoidal_category.

  Context (C : category).

  Definition cat_of_endofunctors := category_from_bicat_and_ob(C:=bicat_of_cats) C.

  Definition monoidal_of_endofunctors: monoidal cat_of_endofunctors:= monoidal_from_bicat_and_ob(C:=bicat_of_cats) C.
  (** we need this high-level view in order to be able to instantiate [montrafotargetbicat_disp_monoidal] in [ActionBasedStrongFunctorsWhiskeredMonoidal] *)

End Endofunctors_as_monoidal_category.
