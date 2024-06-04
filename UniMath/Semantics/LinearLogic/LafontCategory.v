(****************************************************************************

 Lafont Categories

 In this file, we define Lafont categories and we show that every Lafont
 category gives rise to a linear-non-linear model.

 Contents
 1. Lafont category
 2. Every Lafont category gives rise to a linear-non-linear model
 3. Builder for Lafont categories

 ****************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.CommComonoidsCartesian.
Require Import UniMath.Semantics.LinearLogic.LinearNonLinear.

Import MonoidalNotations.

Local Open Scope cat.

(**
 1. Lafont category
 *)
Definition lafont_category
  : UU
  := ∑ (V : sym_mon_closed_cat),
     is_left_adjoint (underlying_commutative_comonoid V).

#[reversible=no] Coercion lafont_category_to_sym_mon_closed_cat
         (V : lafont_category)
  : sym_mon_closed_cat
  := pr1 V.

Definition is_left_adjoint_lafont_category
           (V : lafont_category)
  : is_left_adjoint (underlying_commutative_comonoid V)
  := pr2 V.

(**
 2. Every Lafont category gives rise to a linear-non-linear model
 *)
Definition linear_non_linear_model_from_lafont_category
           (V : lafont_category)
  : linear_non_linear_model.
Proof.
  use make_linear_non_linear_from_strong.
  - exact V.
  - exact (symmetric_cat_commutative_comonoids V).
  - use make_adjunction.
    + use make_adjunction_data.
      * exact (underlying_commutative_comonoid V).
      * exact (right_adjoint (is_left_adjoint_lafont_category V)).
      * exact (adjunit (is_left_adjoint_lafont_category V)).
      * exact (adjcounit (is_left_adjoint_lafont_category V)).
    + exact (pr22 (is_left_adjoint_lafont_category V)).
  - apply cartesian_monoidal_cat_of_comm_comonoids.
  - apply projection_fmonoidal.
  - apply projection_is_symmetric.
Defined.

(**
 3. Builder for Lafont categories

 Note: it is convenient to use `left_adjoint_from_partial` to
 construct Lafont categories.
 *)
Definition make_lafont_category
           (V : sym_mon_closed_cat)
           (HV : is_left_adjoint (underlying_commutative_comonoid V))
  : lafont_category
  := V ,, HV.
