(**********************************************************************************

 The category of bimodules

 Let `R₁` and `R₂` be rings. A bimodule `B` from `R₁` to `R₂` is an abelian group
 together with a linear biaction of `R₁` and `R₂` on `B`. In this file, we define
 the category of bimodules using two-sided displayed categories.

 Contents
 1. Definition via two-sided displayed categories
 2. Univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Categories.AbelianGroup.
Require Import UniMath.CategoryTheory.Categories.Commring.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

(**
 1. Definition via two-sided displayed categories
 *)
Definition bimodule_abgr
  : twosided_disp_cat commring_category commring_category
  := constant_twosided_disp_cat _ _ abelian_group_category.

Definition action_on_bimodule_ob_mor
  : disp_cat_ob_mor (total_twosided_disp_category bimodule_abgr).
Proof.
  simple refine (_ ,, _).
  - exact (λ B,
           let R₁ := (pr1 B : commring) in
           let G := (pr22 B : abgr) in
           let R₂ := (pr12 B : commring) in
           R₁ → G → R₂ → G).
  - cbn.
    exact (λ B₁ B₂,
           let R₁ := (pr1 B₁ : commring) in
           let G := (pr22 B₁ : abgr) in
           let R₂ := (pr12 B₁ : commring) in
           let S₁ := (pr1 B₂ : commring) in
           let H := (pr22 B₂ : abgr) in
           let S₂ := (pr12 B₂ : commring) in
           λ (μ₁ : R₁ → G → R₂ → G) (μ₂ : S₁ → H → S₂ → H) f,
           let f₁ := (pr1 f : R₁ → S₁) in
           let f₂ := (pr12 f : R₂ → S₂) in
           let g := ((pr22 f : abelian_group_morphism _ _) : G → H) in
           ∏ (x : R₁) (y : G) (z : R₂),
           g (μ₁ x y z)
           =
           μ₂ (f₁ x) (g y) (f₂ z)).
Defined.

Definition action_on_bimodule_id_comp
  : disp_cat_id_comp
      (total_twosided_disp_category bimodule_abgr)
      action_on_bimodule_ob_mor.
Proof.
  split.
  - intros B μ x y z ; cbn in *.
    apply idpath.
  - intros B₁ B₂ B₃ f g μ₁ μ₂ μ₃ p q x y z ; cbn in *.
    rewrite p.
    rewrite q.
    apply idpath.
Qed.

Definition action_on_bimodule_data
  : disp_cat_data (total_twosided_disp_category bimodule_abgr).
Proof.
  simple refine (_ ,, _).
  - exact action_on_bimodule_ob_mor.
  - exact action_on_bimodule_id_comp.
Defined.

Definition action_on_bimodule_axioms
  : disp_cat_axioms
      (total_twosided_disp_category bimodule_abgr)
      action_on_bimodule_data.
Proof.
  repeat split.
  - intros B₁ B₂ ; intros.
    repeat (use funextsec ; intro).
    apply (pr11 (pr22 B₂)).
  - intros B₁ B₂ ; intros.
    repeat (use funextsec ; intro).
    apply (pr11 (pr22 B₂)).
  - intros B₁ B₂ B₃ B₄ ; intros.
    repeat (use funextsec ; intro).
    apply (pr11 (pr22 B₄)).
  - intros B₁ B₂ ; intros.
    apply isasetaprop.
    repeat (use impred ; intro).
    apply (pr11 (pr22 B₂)).
Qed.

Definition action_on_bimodule
  : disp_cat (total_twosided_disp_category bimodule_abgr).
Proof.
  simple refine (_ ,, _).
  - exact action_on_bimodule_data.
  - exact action_on_bimodule_axioms.
Defined.

Definition bimodule_action
  : twosided_disp_cat commring_category commring_category
  := sigma_twosided_disp_cat _ action_on_bimodule.

Definition bimodule_laws
           {R S : commring}
           {G : abgr}
           (μ : R → G → S → G)
  : UU
  := (∏ (x : G), μ 1 x 1 = x)%ring
     ×
     (∏ (r₁ r₂ : R) (s₁ s₂ : S) (x : G),
      μ (r₁ * r₂)%ring x (s₁ * s₂)%ring
      =
      μ r₁ (μ r₂ x s₁) s₂)
     ×
     (∏ (r₁ r₂ : R) (s : S) (x : G),
      op (μ r₁ x s) (μ r₂ x s)
      =
      μ (r₁ + r₂)%ring x s)
     ×
     (∏ (r : R) (s : S) (x₁ x₂ : G),
      op (μ r x₁ s) (μ r x₂ s)
      =
      μ r (op x₁ x₂) s)
     ×
     (∏ (r : R) (s₁ s₂ : S) (x : G),
      op (μ r x s₁) (μ r x s₂)
      =
      μ r x (s₁ + s₂)%ring).

Definition isaprop_bimodule_laws
           {R S : commring}
           {G : abgr}
           (μ : R → G → S → G)
  : isaprop (bimodule_laws μ).
Proof.
  repeat (apply isapropdirprod) ;
  repeat (apply impred ; intro) ;
  apply (pr11 G).
Qed.

Definition disp_cat_bimodule_laws
  : disp_cat (total_twosided_disp_category bimodule_action).
Proof.
  use disp_full_sub.
  exact (λ X, bimodule_laws (pr222 X)).
Defined.

Definition bimodule_twosided_disp_cat
  : twosided_disp_cat commring_category commring_category
  := sigma_twosided_disp_cat _ disp_cat_bimodule_laws.

(**
 2. Univalence
 *)
Definition is_univalent_action_on_bimodule
  : is_univalent_disp action_on_bimodule.
Proof.
  intros B₁ B₂ p μ₁ μ₂.
  induction p.
  use isweqimplimpl.
  - cbn ; intro f.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro z.
    exact (pr1 f x y z).
  - cbn in * ; repeat (use funspace_isaset).
    apply (pr11 (pr22 B₁)).
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      repeat (use funextsec ; intro).
      apply (pr11 (pr22 B₁)).
Qed.

Definition is_univalent_disp_cat_bimodule_laws
  : is_univalent_disp disp_cat_bimodule_laws.
Proof.
  use disp_full_sub_univalent.
  intro.
  apply isaprop_bimodule_laws.
Defined.

Definition is_univalent_bimodule_twosided_disp_cat
  : is_univalent_twosided_disp_cat bimodule_twosided_disp_cat.
Proof.
  use is_univalent_sigma_of_twosided_disp_cat.
  - use is_univalent_sigma_of_twosided_disp_cat.
    + use is_univalent_constant_twosided_disp_cat.
      exact is_univalent_abelian_group_category.
    + exact is_univalent_action_on_bimodule.
  - exact is_univalent_disp_cat_bimodule_laws.
Qed.
