(*********************************************
State

A state in a Markov category C is pair (X,p) of an object equipped with a distribution I --> x.

Here, we define states as a reuseable notion. States form for example the objects of the slice category
I/C, as well as the categories of probability spaces and couplings over a Markov category C. 

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
Local Open Scope markov.

Definition state (C : markov_category) := ∑ (x : C), I_{C} --> x.

Definition state_ob {C : markov_category} (p : state C) : C := pr1 p.

Coercion state_mor {C : markov_category} (p : state C) : I_{C} --> state_ob p
  := pr2 p.

Definition faithful {C : markov_category} {y : C} (p : state C) : UU
  := ∏ (f g : state_ob p --> y), (f =_{p} g) -> f = g.