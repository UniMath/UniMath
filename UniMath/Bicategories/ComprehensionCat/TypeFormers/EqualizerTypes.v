(*******************************************************************************************

 Comprehension categories with equalizers types

 In this file, we define the displayed bicategory of equalizer types for comprehension
 categories, and we show that this displayed bicategory is univalent. Note that equalizer types
 can be phrased solely using the fibration of types, and for that reason, we define a displayed
 bicategory of the bicategory of categories with a terminal object and a cleaving. Since we
 are using univalent categories, we define this displayed bicategory as a subbicategory,
 because equalizers are unique up to isomorphism. We then lift this displayed bicategory to
 comprehension categories and to full comprehension categories.

 It is important to notice equalizer types are a bit different from extensional identity
 types. Whereas identity types are defined via a left adjoint of the diagonal substitution,
 equalizer types are defined by stating that every fiber has equalizers that are preserved
 under substitution. However, if a comprehension category has fiberwise equalizers, then one
 can construct identity types. For the converse, one needs dependent sums (Theorem 10.5.10 in
 'Categorical Logic and Type Theory' by Jacobs).

 References:
 - 'Categorical Logic and Type Theory' by Jacobs

 Contents
 1. The displayed bicategory of equalizer types
 2. The univalence of this displayed bicategory
 3. Equalizer types for comprehension categories
 4. Equalizer types for full comprehension categories

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

(** * 1. The displayed bicategory of equalizer types *)
Definition disp_bicat_of_equalizer_type
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat.
  - exact (λ (C : cat_with_terminal_cleaving),
           fiberwise_equalizers (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : cat_with_terminal_cleaving)
             (T₁ : fiberwise_equalizers (cleaving_of_types C₁))
             (T₂ : fiberwise_equalizers (cleaving_of_types C₂))
             (F : functor_with_terminal_cleaving C₁ C₂),
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

(** * 2. The univalence of this displayed bicategory *)
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
  - exact is_univalent_2_bicat_cat_with_terminal_cleaving.
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

Definition disp_2cells_isaprop_disp_bicat_of_equalizer_type
  : disp_2cells_isaprop disp_bicat_of_equalizer_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_equalizer_type
  : disp_locally_groupoid disp_bicat_of_equalizer_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

(** * 3. Equalizer types for comprehension categories *)
Definition disp_bicat_of_equalizer_type_comp_cat
  : disp_bicat bicat_comp_cat
  := lift_disp_bicat _ disp_bicat_of_equalizer_type.

Definition univalent_2_1_disp_bicat_of_equalizer_type_comp_cat
  : disp_univalent_2_1 disp_bicat_of_equalizer_type_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_equalizer_type.
Qed.

Definition univalent_2_0_disp_bicat_of_equalizer_type_comp_cat
  : disp_univalent_2_0 disp_bicat_of_equalizer_type_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_equalizer_type.
  - exact univalent_2_1_disp_bicat_of_equalizer_type.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_equalizer_type_comp_cat
  : disp_univalent_2 disp_bicat_of_equalizer_type_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_equalizer_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_equalizer_type_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_equalizer_type_comp_cat
  : disp_2cells_isaprop disp_bicat_of_equalizer_type_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_equalizer_type.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_equalizer_type_comp_cat
  : disp_locally_groupoid disp_bicat_of_equalizer_type_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_equalizer_type.
Qed.

(** * 4. Equalizer types for full comprehension categories *)
Definition disp_bicat_of_equalizer_type_full_comp_cat
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_equalizer_type_comp_cat.

Definition univalent_2_1_disp_bicat_of_equalizer_type_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_equalizer_type_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_equalizer_type_comp_cat.
Qed.

Definition univalent_2_0_disp_bicat_of_equalizer_type_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_equalizer_type_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_equalizer_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_equalizer_type_comp_cat.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_equalizer_type_full_comp_cat
  : disp_univalent_2 disp_bicat_of_equalizer_type_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_equalizer_type_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_equalizer_type_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_equalizer_type_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_equalizer_type_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_equalizer_type_comp_cat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_equalizer_type_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_equalizer_type_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_equalizer_type_comp_cat.
Qed.
