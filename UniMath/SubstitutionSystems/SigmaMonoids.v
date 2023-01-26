(** a generalization of Σ-monoids to monoidal categories in place of functor categories

author: Kobe Wullaert 2023
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.

Local Open Scope cat.

Import BifunctorNotations.

Section SigmaMonoid.

  Context {V : category}
          {Mon_V : monoidal V}
          {H : V ⟶ V}
          (θ : pointedtensorialstrength Mon_V H).

  Definition SigmaMonoid_disp_cat_no_compatibility : disp_cat V
    := dirprod_disp_cat (algebra_disp_cat H) (monoid_disp_cat Mon_V).

  Definition SigmaMonoid_compatibility
             (X : total_category SigmaMonoid_disp_cat_no_compatibility) : UU.
  Proof.
    set (x := pr1 X).
    set (η := monoid_data_unit _ (pr22 X : monoid _ _)).
    set (μ := monoid_data_multiplication _ (pr22 X : monoid _ _)).
    set (α := pr12 X).
    set (st := pr1 θ (x ,, η) x).
    exact (st · (#H μ) · α = x ⊗^{Mon_V}_{l} α · μ).
  Defined.

  Definition SigmaMonoid_disp_cat_without_sigma_constr
    : disp_cat (total_category SigmaMonoid_disp_cat_no_compatibility)
    := disp_full_sub
         (total_category SigmaMonoid_disp_cat_no_compatibility)
         SigmaMonoid_compatibility.

  Definition SigmaMonoid_disp_cat
    : disp_cat V
    := sigma_disp_cat SigmaMonoid_disp_cat_without_sigma_constr.

  Definition SigmaMonoid : category
    := total_category SigmaMonoid_disp_cat.

End SigmaMonoid.

Section GHSS_to_SigmaMonoid.

  Context {V : category}
          {Mon_V : monoidal V}
          {H : V ⟶ V}
          (θ : pointedtensorialstrength Mon_V H).

  Definition ghhs_to_sigma_monoid (t : ghss Mon_V H θ)
    : SigmaMonoid θ.
  Proof.
    exists (pr1 t).
    exists (tau_from_alg Mon_V H θ t ,, ghss_monoid Mon_V H θ t).
    exact (gfbracket_τ Mon_V H θ t (Z :=  (pr1 t,, μ_0 Mon_V H θ t)) (identity _)).
  Defined.

End GHSS_to_SigmaMonoid.
