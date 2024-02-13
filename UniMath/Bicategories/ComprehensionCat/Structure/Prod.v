Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

Definition disp_bicat_of_prod_type
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : full_comp_cat), fiberwise_binproducts (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : full_comp_cat)
             (T₁ : fiberwise_binproducts (cleaving_of_types C₁))
             (T₂ : fiberwise_binproducts (cleaving_of_types C₂))
             (F : full_comp_cat_functor C₁ C₂),
           ∏ (x : C₁),
           preserves_binproduct
             (fiber_functor (comp_cat_type_functor F) x)).
  - abstract
      (intros C P x y₁ y₂ p π₁ π₂ H ;
       exact H).
  - abstract
      (intros C₁ C₂ C₃ P₁ P₂ P₃ F G HF HG x y₁ y₂ p π₁ π₂ H ;
       use (isBinProduct_eq_arrow _ _
              (composition_preserves_binproduct (HF x) (HG _) _ _ _ _ _ H)) ;
       cbn ;
       rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
Defined.

Definition univalent_2_1_disp_bicat_of_prod_type
  : disp_univalent_2_1 disp_bicat_of_prod_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  use impred ; intro.
  apply isaprop_preserves_binproduct.
Qed.

Definition univalent_2_0_disp_bicat_of_prod_type
  : disp_univalent_2_0 disp_bicat_of_prod_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    apply isaprop_fiberwise_binproducts.
  - intros C₁ C₂ T₁ T₂ f.
    use impred ; intro.
    apply isaprop_preserves_binproduct.
Qed.

Definition univalent_2_disp_bicat_of_prod_type
  : disp_univalent_2 disp_bicat_of_prod_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_prod_type.
  - exact univalent_2_1_disp_bicat_of_prod_type.
Defined.
