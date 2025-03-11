(**************************************************************************************************

  Reflexive Objects

  A reflexive object is an object X with a retract onto the exponential object X^X. Here, we package
  all the data together: the category with a terminal and binary products, the object with an
  exponential, and the retraction. We define a constructor and accessors.

  Contents
  1. Reflexive objects, with a constructor and accessors [reflexive_objects]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Definition reflexive_object
  : UU
  := ∑ (C : ∑ (C : category), Terminal C × BinProducts C)
      (X : ∑ (X : pr1 C), is_exponentiable (pr22 C) X),
      retraction (exp (pr2 X) (pr1 X)) (pr1 X).

Definition make_reflexive_object
  (C : category)
  (T : Terminal C)
  (BP : BinProducts C)
  (X : C)
  (E : is_exponentiable BP X)
  (abs : C⟦exp E X, X⟧)
  (app : C⟦X, exp E X⟧)
  (H : is_retraction abs app)
  : reflexive_object
  := (C ,, T ,, BP) ,, (X ,, E) ,, (abs ,, app ,, H).

Definition reflexive_object_category
  (X : reflexive_object)
  : category
  := pr11 X.

Definition reflexive_object_Terminal
  (X : reflexive_object)
  : Terminal (reflexive_object_category X)
  := pr121 X.

Definition reflexive_object_BinProducts
  (X : reflexive_object)
  : BinProducts (reflexive_object_category X)
  := pr221 X.

Coercion reflexive_object_object
  (X : reflexive_object)
  : reflexive_object_category X
  := pr112 X.

Definition reflexive_object_exponentiable
  (X : reflexive_object)
  : is_exponentiable (reflexive_object_BinProducts X) X
  := pr212 X.

Definition reflexive_object_abs
  (X : reflexive_object)
  : exp (reflexive_object_exponentiable X) X --> X
  := retraction_section (pr22 X).

Definition reflexive_object_app
  (X : reflexive_object)
  : X --> exp (reflexive_object_exponentiable X) X
  := pr22 X.

Definition reflexive_object_is_reflexive
  (X : reflexive_object)
  : is_retraction (reflexive_object_abs X) (reflexive_object_app X)
  := retraction_is_retraction (pr22 X).
