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
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
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

Definition disp_bicat_of_equalizer_type
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : full_comp_cat), fiberwise_equalizers (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : full_comp_cat)
             (T₁ : fiberwise_equalizers (cleaving_of_types C₁))
             (T₂ : fiberwise_equalizers (cleaving_of_types C₂))
             (F : full_comp_cat_functor C₁ C₂),
           ∏ (x : C₁),
           preserves_equalizer
             (fiber_functor (comp_cat_type_functor F) x)).
  - abstract
      (intros C EC x y₁ y₂ e f g h p Fp H ;
       exact H).
  - intros C₁ C₂ C₃ EC₁ EC₂ EC₃ F G HF HG x y₁ y₂ e f g h p Fp H.
    use (isEqualizer_eq
           _ _ _ _ _
           (composition_preserves_equalizer (HF x) (HG _) _ _ _ _ _ _ _ _ H)).
    + abstract
        (cbn ;
         rewrite !mor_disp_transportf_prewhisker ;
         rewrite !mor_disp_transportf_postwhisker ;
         rewrite !disp_functor_transportf ;
         rewrite !mor_disp_transportf_prewhisker ;
         rewrite !mor_disp_transportf_postwhisker ;
         rewrite <- !disp_functor_comp_var ;
         rewrite !disp_functor_transportf ;
         rewrite !transport_f_f ;
         pose (maponpaths (transportb _ (id_right _)) p) as p' ;
         cbn in p' ;
         rewrite !transportbfinv in p' ;
         rewrite p' ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         rewrite !disp_functor_transportf ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         rewrite !disp_functor_transportf ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         rewrite !disp_functor_transportf ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition univalent_2_1_disp_bicat_of_equalizer_type
  : disp_univalent_2_1 disp_bicat_of_equalizer_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  use impred ; intro.
  apply isaprop_preserves_equalizer.
Qed.

Definition univalent_2_0_disp_bicat_of_equalizer_type
  : disp_univalent_2_0 disp_bicat_of_equalizer_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    apply isaprop_fiberwise_equalizers.
  - intros C₁ C₂ T₁ T₂ f.
    use impred ; intro.
    apply isaprop_preserves_equalizer.
Qed.

Definition univalent_2_disp_bicat_of_equalizer_type
  : disp_univalent_2 disp_bicat_of_equalizer_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_equalizer_type.
  - exact univalent_2_1_disp_bicat_of_equalizer_type.
Defined.
