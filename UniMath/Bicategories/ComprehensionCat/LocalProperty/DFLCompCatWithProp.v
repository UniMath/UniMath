(*******************************************************************************************

 DFL full comprehension categories with fiberwise structure

 In this file, we define the bicategory of DFL full comprehension category that support some
 fiberwise structure. We do this in multiple steps. First, we define a displayed bicategory
 over the bicategory of categories with a cleaving and a terminal object such that this
 cleaving satisfies some categorical property fiberwise. This means that every fiber has
 the desired structure and that the structure is preserved by taking pullbacks. A concrete
 example would be given by the following categorical property:
 - A category satisfies the property if it has a terminal object
 - A functor preserves the property if it preserves terminal objects
 A fibration satisfies this property fiberwise if every fiber has a terminal object and if
 taking pullbacks preserves terminal objects.

 We then lift this displayed bicategories to comprehension categories, full comprehension
 categories, and to DFL comprehension categories. On the way, we also classify the displayed
 adjoint equivalences in these displayed bicategories.

 Contents
 1. The bicategory of fibrations with fiberwise structure
 2. The bicategory of comprehension categories with fiberwise structure
 3. The bicategory of full comprehension categories with fiberwise structure
 4. The bicategory of DFL comprehension categories with fiberwise structure

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.

Local Open Scope cat.

(** * 1. The bicategory of fibrations with fiberwise structure *)
Definition disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat.
  - exact (λ (C : cat_with_terminal_cleaving),
           fiberwise_cat_property P (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : cat_with_terminal_cleaving)
             (H₁ : fiberwise_cat_property P (cleaving_of_types C₁))
             (H₂ : fiberwise_cat_property P (cleaving_of_types C₂))
             (F : functor_with_terminal_cleaving C₁ C₂),
           fiberwise_cat_property_functor (comp_cat_type_functor F) H₁ H₂).
  - abstract
      (intros C H x ;
       apply (cat_property_fiber_functor_id P x)).
  - abstract
      (intros C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG x ;
       exact (cat_property_fiber_functor_comp P (HF x) (HG _))).
Defined.

Definition univalent_2_1_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_fiberwise_cat_property P).
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ H₁ H₂ F.
  use impred ; intro.
  apply (@isaprop_cat_property_functor
            P
            (univalent_fiber_category _ _)
            (univalent_fiber_category _ _)).
Qed.

Definition univalent_2_0_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_fiberwise_cat_property P).
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_with_terminal_cleaving.
  - intro C.
    apply isaprop_fiberwise_cat_property.
  - intros.
    use impred ; intro.
    apply (@isaprop_cat_property_functor
              P
              (univalent_fiber_category _ _)
              (univalent_fiber_category _ _)).
Qed.

Definition univalent_2_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_fiberwise_cat_property P).
Proof.
  split.
  - exact (univalent_2_0_disp_bicat_of_fiberwise_cat_property P).
  - exact (univalent_2_1_disp_bicat_of_fiberwise_cat_property P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_fiberwise_cat_property P).
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_fiberwise_cat_property P).
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_fiberwise_cat_property
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_fiberwise_cat_property P).
Proof.
  apply disp_2cells_iscontr_subbicat.
Qed.

Definition fiberwise_cat_property_functor_adjequiv
           {P : cat_property}
           {C₁ C₂ : bicat_cat_with_terminal_cleaving}
           (F : adjoint_equivalence C₁ C₂)
           (H₁ : fiberwise_cat_property P (cleaving_of_types C₁))
           (H₂ : fiberwise_cat_property P (cleaving_of_types C₂))
  : fiberwise_cat_property_functor (comp_cat_type_functor (pr11 F)) H₁ H₂.
Proof.
  revert C₁ C₂ F P H₁ H₂.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  }
  intros C P H₁ H₂ ; cbn.
  intro ; cbn.
  assert (H₁ x = H₂ x) as p .
  {
    apply (isaprop_cat_property_ob P (univalent_fiber_category _ _)).
  }
  refine (transportf
            (λ z, cat_property_functor _ _ z _)
            p
            _).
  apply cat_property_fiber_functor_id.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_fiberwise_cat_property_help
           {P : cat_property}
           {C₁ C₂ : bicat_cat_with_terminal_cleaving}
           (F : adjoint_equivalence C₁ C₂)
           {H₁ : disp_bicat_of_fiberwise_cat_property P C₁}
           {H₂ : disp_bicat_of_fiberwise_cat_property P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P H₁ H₂ FF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  }
  intros C P H₁ H₂ FF.
  use disp_left_adjoint_equivalence_subbicat.
  - clear C H₁ H₂ FF.
    intros C₁ C₂ H₁ H₂ F HF.
    apply (fiberwise_cat_property_functor_adjequiv (F ,, HF)).
  - exact is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_fiberwise_cat_property
           {P : cat_property}
           {C₁ C₂ : bicat_cat_with_terminal_cleaving}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {H₁ : disp_bicat_of_fiberwise_cat_property P C₁}
           {H₂ : disp_bicat_of_fiberwise_cat_property P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_cat_fiberwise_cat_property_help
           (F ,, HF)
           FF).
Qed.

(** * 2. The bicategory of comprehension categories with fiberwise structure *)
Definition disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_bicat bicat_comp_cat
  := lift_disp_bicat _ (disp_bicat_of_fiberwise_cat_property P).

Definition univalent_2_1_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_cat_property_comp_cat P).
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact (univalent_2_1_disp_bicat_of_fiberwise_cat_property P).
Qed.

Definition univalent_2_0_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_cat_property_comp_cat P).
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact (univalent_2_0_disp_bicat_of_fiberwise_cat_property P).
  - exact (univalent_2_1_disp_bicat_of_fiberwise_cat_property P).
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_cat_property_comp_cat P).
Proof.
  split.
  - exact (univalent_2_0_disp_bicat_of_cat_property_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_comp_cat P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_cat_property_comp_cat P).
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact (disp_2cells_isaprop_disp_bicat_of_fiberwise_cat_property P).
Qed.

Definition disp_locally_groupoid_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_cat_property_comp_cat P).
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact (disp_locally_groupoid_disp_bicat_of_fiberwise_cat_property P).
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_cat_property_comp_cat
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_cat_property_comp_cat P).
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  apply disp_2cells_iscontr_disp_bicat_of_fiberwise_cat_property.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_comp_cat_help
           {P : cat_property}
           {C₁ C₂ : bicat_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {H₁ : disp_bicat_of_cat_property_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P H₁ H₂ FF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_comp_cat.
  }
  intros C P T₁ T₂ FF.
  use to_disp_left_adjoint_equivalence_over_id_lift.
  apply disp_adjoint_equiv_disp_bicat_of_fiberwise_cat_property.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_comp_cat
           {P : cat_property}
           {C₁ C₂ : bicat_comp_cat}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {H₁ : disp_bicat_of_cat_property_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  apply (disp_adjoint_equiv_disp_bicat_of_cat_property_comp_cat_help (F ,, HF)).
Qed.

(** * 3. The bicategory of full comprehension categories with fiberwise structure *)
Definition disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat _ (disp_bicat_of_cat_property_comp_cat P).

Definition univalent_2_1_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact (univalent_2_1_disp_bicat_of_cat_property_comp_cat P).
Qed.

Definition univalent_2_0_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact (univalent_2_0_disp_bicat_of_cat_property_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_comp_cat P).
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  split.
  - exact (univalent_2_0_disp_bicat_of_cat_property_full_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_full_comp_cat P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact (disp_2cells_isaprop_disp_bicat_of_cat_property_comp_cat P).
Qed.

Definition disp_locally_groupoid_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact (disp_locally_groupoid_disp_bicat_of_cat_property_comp_cat P).
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_cat_property_full_comp_cat
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_cat_property_full_comp_cat P).
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  apply disp_2cells_iscontr_disp_bicat_of_cat_property_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_full_comp_cat_help
           {P : cat_property}
           {C₁ C₂ : bicat_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {H₁ : disp_bicat_of_cat_property_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P H₁ H₂ FF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_full_comp_cat.
  }
  intros C P T₁ T₂ FF.
  use to_disp_left_adjoint_equivalence_over_id_lift.
  apply disp_adjoint_equiv_disp_bicat_of_cat_property_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_full_comp_cat
           {P : cat_property}
           {C₁ C₂ : bicat_full_comp_cat}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {H₁ : disp_bicat_of_cat_property_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  apply (disp_adjoint_equiv_disp_bicat_of_cat_property_full_comp_cat_help (F ,, HF)).
Qed.

(** * 4. The bicategory of DFL comprehension categories with fiberwise structure *)
Definition disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_bicat bicat_of_dfl_full_comp_cat
  := lift_disp_bicat _ (disp_bicat_of_cat_property_full_comp_cat P).

Definition univalent_2_1_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact (univalent_2_1_disp_bicat_of_cat_property_full_comp_cat P).
Qed.

Definition univalent_2_0_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact (univalent_2_0_disp_bicat_of_cat_property_full_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_full_comp_cat P).
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  split.
  - exact (univalent_2_0_disp_bicat_of_cat_property_dfl_full_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_dfl_full_comp_cat P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact (disp_2cells_isaprop_disp_bicat_of_cat_property_full_comp_cat P).
Qed.

Definition disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact (disp_locally_groupoid_disp_bicat_of_cat_property_full_comp_cat P).
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  apply disp_2cells_iscontr_disp_bicat_of_cat_property_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat_help
           {P : cat_property}
           {C₁ C₂ : bicat_of_dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {H₁ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P H₁ H₂ FF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C P T₁ T₂ FF.
  use to_disp_left_adjoint_equivalence_over_id_lift.
  apply disp_adjoint_equiv_disp_bicat_of_cat_property_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat
           {P : cat_property}
           {C₁ C₂ : bicat_of_dfl_full_comp_cat}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {H₁ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  apply (disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat_help (F ,, HF)).
Qed.
