(*********************************************************************************

 Cartesian monoidal categories

 In this file, we discuss several variations of cartesian monoidal categories.

 Contents
 1. Cartesan monoidal categories
 2. Cocartesian monoidal categories

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.

(**
 1. Cartesan monoidal categories
 *)
Definition is_semicartesian
           {C : category}
           (M : monoidal C)
  : UU
  := isTerminal C (I_{M}).

Definition tensor_isBinProduct
           {C : category}
           (M : monoidal C)
  : UU
  := ∏ (x y : C),
     ∑ (π₁ : x ⊗_{M} y --> x) (π₂ : x ⊗_{M} y --> y),
     isBinProduct _ _ _ _ π₁ π₂.

Definition is_cartesian
           {C : category}
           (M : monoidal C)
  : UU
  := is_semicartesian M × tensor_isBinProduct M.

(**
 2. Cocartesian monoidal categories
 *)
Definition is_semicocartesian
           {C : category}
           (M : monoidal C)
  : UU
  := isInitial C (I_{M}).

Definition tensor_isBinCoproduct
           {C : category}
           (M : monoidal C)
  : UU
  := ∏ (x y : C),
     ∑ (ι₁ : x --> x ⊗_{M} y) (ι₂ : y --> x ⊗_{M} y),
     isBinCoproduct _ _ _ _ ι₁ ι₂.

Definition is_cocartesian
           {C : category}
           (M : monoidal C)
  : UU
  := is_semicocartesian M × tensor_isBinCoproduct M.
