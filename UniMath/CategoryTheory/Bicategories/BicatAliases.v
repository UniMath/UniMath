(* ******************************************************************************* *)
(** * Bicategories

Definition of aliases for the names defined in Bicategories/Bicat

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Local Open Scope cat.

(* -----------------------------------------------------------------------------------*)
(** ** Notations.                                                                     *)
(* -----------------------------------------------------------------------------------*)


Notation "'id₁'" := identity.
Notation "'id₂'" := id2.
Notation " b ⋆⋆ a" := (a ⋆ b) (at level 30).
