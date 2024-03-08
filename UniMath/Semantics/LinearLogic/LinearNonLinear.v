(****************************************************************************

 Linear-non-linear models of linear logic

 In this file, we define the notion of linear-non-linear models, which is
 one of the basic notions of models for linear logic. See for example
 - "Categorical Semantics of Linear Logic"
 - "A Mixed Linear Non-Linear Logic: Proofs, Terms, and Models"
 - "Categorical Models of Linear Logic Revisited"
 We also give a symmetric monoidal comonad arising from these models, which
 gives an interpretation to the !-modality.

 Contents
 1. Linear-non-linear models
 2. Accessors and builders
 3. !-modality

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
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Import MonoidalNotations.

Local Open Scope cat.

(**
 1. Linear-non-linear models
 *)
Definition linear_non_linear_model
  : UU
  := ∑ (𝕃 : sym_mon_closed_cat) (* \bL *)
       (𝕄 : sym_monoidal_cat) (* \bM *)
       (A : adjunction 𝕄 𝕃),
     is_cartesian 𝕄
     ×
     sym_monoidal_adjunction 𝕄 𝕃 A.

(**
 2. Accessors and builders
 *)
#[reversible=no] Coercion linear_non_linear_model_to_linear
         (𝕃 : linear_non_linear_model)
  : sym_mon_closed_cat
  := pr1 𝕃.

Definition cartesian_cat_from_linear_non_linear_model
           (𝕃 : linear_non_linear_model)
  : sym_monoidal_cat
  := pr12 𝕃.

Definition adjunction_from_linear_non_linear_model
           (𝕃 : linear_non_linear_model)
  : adjunction
      (cartesian_cat_from_linear_non_linear_model 𝕃)
      𝕃
  := pr122 𝕃.

Proposition is_cartesian_cat_from_linear_non_linear_model
            (𝕃 : linear_non_linear_model)
  : is_cartesian (cartesian_cat_from_linear_non_linear_model 𝕃).
Proof.
  exact (pr1 (pr222 𝕃)).
Qed.

Definition sym_monoidal_adjunction_from_linear_non_linear_model
           (𝕃 : linear_non_linear_model)
  : sym_monoidal_adjunction
      (cartesian_cat_from_linear_non_linear_model 𝕃)
      𝕃
      (adjunction_from_linear_non_linear_model 𝕃)
  := pr2 (pr222 𝕃).

Definition make_linear_non_linear
           (𝕃 : sym_mon_closed_cat)
           (𝕄 : sym_monoidal_cat)
           (A : adjunction 𝕄 𝕃)
           (HM : is_cartesian 𝕄)
           (HA : sym_monoidal_adjunction 𝕄 𝕃 A)
  : linear_non_linear_model
  := 𝕃 ,, 𝕄 ,, A ,, HM ,, HA.

Definition make_linear_non_linear_from_strong
           (𝕃 : sym_mon_closed_cat)
           (𝕄 : sym_monoidal_cat)
           (A : adjunction 𝕄 𝕃)
           (HM : is_cartesian 𝕄)
           (HL₁ : fmonoidal 𝕄 𝕃 (left_adjoint A))
           (HL₂ : is_symmetric_monoidal_functor 𝕄 𝕃 HL₁)
  : linear_non_linear_model.
Proof.
  use make_linear_non_linear.
  - exact 𝕃.
  - exact 𝕄.
  - exact A.
  - exact HM.
  - use sym_monoidal_adjunction_from_strong.
    + exact HL₁.
    + exact HL₂.
Defined.

(**
 3. !-modality
 *)
Definition bang_modality
           (𝕃 : linear_non_linear_model)
  : sym_monoidal_cmd 𝕃
  := sym_monoidal_adjunction_to_sym_monoidal_cmd
       (adjunction_from_linear_non_linear_model 𝕃)
       (sym_monoidal_adjunction_from_linear_non_linear_model 𝕃).
