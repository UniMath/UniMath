(*********************************************
State

[...] states in markov categories

Todo: add faithfulness

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.Quotient.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Definition state (C : markov_category) := ∑ (x : C), I_{C} --> x.

Definition state_ob {C : markov_category} (p : state C) : C := pr1 p.

Coercion state_mor {C : markov_category} (p : state C) : I_{C} --> state_ob p
  := pr2 p.


