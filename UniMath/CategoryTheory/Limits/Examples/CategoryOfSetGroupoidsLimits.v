(**********************************************************************************************

 Limits of setgroupoid

 In this file, we give examples of limits of setgroupoids. Currently, we only consider terminal
 objects, and the terminal setgroupoid is given by the unit category.

 Content
 1. The terminal setgroupoid

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetGroupoids.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Local Open Scope cat.

(** * 1. The terminal setgroupoid *)
Definition terminal_setgroupoid
  : setgroupoid.
Proof.
  use make_setgroupoid.
  - use make_setcategory.
    + exact unit_category.
    + apply isasetunit.
  - exact (pr2 (path_univalent_groupoid (hlevelntosn 2 unit (hlevelntosn 1 unit isapropunit)))).
Defined.

Proposition terminal_obj_setgroupoid_eq
            {G : setgroupoid}
            (F : G ⟶ terminal_setgroupoid)
  : F = functor_to_unit G.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  use functor_data_eq_alt.
  - intro x.
    apply isapropunit.
  - intros x y f.
    apply isasetunit.
Qed.

Definition terminal_obj_setgroupoid
  : Terminal cat_of_setgroupoid.
Proof.
  use make_Terminal.
  - exact terminal_setgroupoid.
  - intros G.
    simple refine (_ ,, _).
    + apply functor_to_unit.
    + intro F.
      exact (terminal_obj_setgroupoid_eq F).
Defined.
