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
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.

Local Open Scope cat.

Import BifunctorNotations.

Definition SigmaMonoid_characteristic_equation {V : category} {Mon_V : monoidal V} {H : V ⟶ V}
    (x : V) (η : V ⟦ monoidal_unit Mon_V, x ⟧)
    (μ : V ⟦ x ⊗_{ Mon_V} x, x ⟧) (τ :  V ⟦ H x, x ⟧)
    (st : V ⟦ x ⊗_{ Mon_V} H x, H (x ⊗_{ Mon_V} x) ⟧) : UU
    := st · #H μ · τ = x ⊗^{Mon_V}_{l} τ · μ.

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
    set (τ := pr12 X : H x --> x).
    set (st := pr1 θ (x ,, η) x).
    exact (SigmaMonoid_characteristic_equation x η μ τ st).
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

  Definition SigmaMonoid_carrier (σ : SigmaMonoid) : V := pr1 σ.
  Definition SigmaMonoid_η (σ : SigmaMonoid) : V ⟦ monoidal_unit Mon_V, SigmaMonoid_carrier σ ⟧
    := monoid_data_unit _ (pr212 σ : monoid _ _).
  Definition SigmaMonoid_μ (σ : SigmaMonoid) :
    V ⟦ SigmaMonoid_carrier σ ⊗_{ Mon_V} SigmaMonoid_carrier σ, SigmaMonoid_carrier σ ⟧
    := monoid_data_multiplication _ (pr212 σ : monoid _ _).
  Definition SigmaMonoid_τ (σ : SigmaMonoid) : V ⟦ H (SigmaMonoid_carrier σ), SigmaMonoid_carrier σ⟧
    := pr112 σ.

  Lemma SigmaMonoid_is_compatible (σ : SigmaMonoid) :
    SigmaMonoid_characteristic_equation (SigmaMonoid_carrier σ)
      (SigmaMonoid_η σ) (SigmaMonoid_μ σ) (SigmaMonoid_τ σ)
      (pr1 θ (SigmaMonoid_carrier σ ,, SigmaMonoid_η σ) (SigmaMonoid_carrier σ)).
  Proof.
    exact (pr22 σ).
  Qed.

  Let MON := category_of_monoids_in_monoidal_cat Mon_V.

  (** the following should be an instance of general results on projection into constituents *)
  Definition SigmaMonoid_to_monoid_data : functor_data SigmaMonoid MON.
  Proof.
    use make_functor_data.
    - intro σ. exact (pr1 σ,, pr212 σ).
    - intros σ1 σ2 m. exact (pr1 m,, pr212 m).
  Defined.

  Lemma SigmaMonoid_to_monoid_laws : is_functor SigmaMonoid_to_monoid_data.
  Proof.
    split.
    - intro. apply idpath.
    - intro; intros. apply idpath.
  Qed.

  Definition SigmaMonoid_to_monoid : functor SigmaMonoid MON :=
    SigmaMonoid_to_monoid_data,,SigmaMonoid_to_monoid_laws.

End SigmaMonoid.

Section MHSS_to_SigmaMonoid.

  Context {V : category}
          {Mon_V : monoidal V}
          {H : V ⟶ V}
          (θ : pointedtensorialstrength Mon_V H).

  Definition mhss_to_sigma_monoid (t : mhss Mon_V H θ)
    : SigmaMonoid θ.
  Proof.
    exists (pr1 t).
    exists (tau_from_alg Mon_V H θ t ,, mhss_monoid Mon_V H θ t).
    exact (mfbracket_τ Mon_V H θ t (Z :=  (pr1 t,, μ_0 Mon_V H θ t)) (identity _)).
  Defined.

End MHSS_to_SigmaMonoid.
