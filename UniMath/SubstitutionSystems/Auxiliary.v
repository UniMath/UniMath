(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Various helper lemmas that should be moved upstream


************************************************************)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
