(*******************************************************************************************

 Comprehension categories with unit types

 In this file, we define the displayed bicategory of unit types for comprehension categories,
 and we show that this displayed bicategory is univalent. Note that unit types can be
 phrased solely using the fibration of types, and for that reason, we define a displayed
 bicategory of the bicategory of categories with a terminal object and a cleaving. Since we
 are using univalent categories, we define this displayed bicategory as a subbicategory,
 because terminal objects are unique up to isomorphism. We then lift this displayed bicategory
 to comprehension categories and to full comprehension categories.

 Contents
 1. The displayed bicategory of unit types
 2. The univalence of this displayed bicategory
 3. Unit types for comprehension categories
 4. Unit types for full comprehension categories
 5. Adjoint equivalences
 6. Strong unit types

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The displayed bicategory of unit types *)
Definition disp_bicat_of_unit_type
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat.
  - exact (λ (C : cat_with_terminal_cleaving),
           fiberwise_terminal (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : cat_with_terminal_cleaving)
             (T₁ : fiberwise_terminal (cleaving_of_types C₁))
             (T₂ : fiberwise_terminal (cleaving_of_types C₂))
             (F : functor_with_terminal_cleaving C₁ C₂),
           ∏ (x : C₁),
           preserves_terminal
             (fiber_functor (comp_cat_type_functor F) x)).
  - abstract
      (intros C T x y Hy ;
       exact Hy).
  - abstract
      (intros C₁ C₂ C₃ T₁ T₂ T₃ F G HF HG x y Hy ;
       apply HG ;
       apply HF ;
       exact Hy).
Defined.

(** * 2. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_unit_type
  : disp_univalent_2_1 disp_bicat_of_unit_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  use impred ; intro.
  apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_0_disp_bicat_of_unit_type
  : disp_univalent_2_0 disp_bicat_of_unit_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_with_terminal_cleaving.
  - intro C.
    apply isaprop_fiberwise_terminal.
  - intros C₁ C₂ T₁ T₂ f.
    use impred ; intro.
    apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_disp_bicat_of_unit_type
  : disp_univalent_2 disp_bicat_of_unit_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_unit_type.
  - exact univalent_2_1_disp_bicat_of_unit_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_unit_type
  : disp_2cells_isaprop disp_bicat_of_unit_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_unit_type
  : disp_locally_groupoid disp_bicat_of_unit_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

(** * 3. Unit types for comprehension categories *)
Definition disp_bicat_of_unit_type_comp_cat
  : disp_bicat bicat_comp_cat
  := lift_disp_bicat _ disp_bicat_of_unit_type.

Definition univalent_2_1_disp_bicat_of_unit_type_comp_cat
  : disp_univalent_2_1 disp_bicat_of_unit_type_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_unit_type.
Qed.

Definition univalent_2_0_disp_bicat_of_unit_type_comp_cat
  : disp_univalent_2_0 disp_bicat_of_unit_type_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_unit_type.
  - exact univalent_2_1_disp_bicat_of_unit_type.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_unit_type_comp_cat
  : disp_univalent_2 disp_bicat_of_unit_type_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_unit_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_unit_type_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_unit_type_comp_cat
  : disp_2cells_isaprop disp_bicat_of_unit_type_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_unit_type.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_unit_type_comp_cat
  : disp_locally_groupoid disp_bicat_of_unit_type_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_unit_type.
Qed.

(** * 4. Unit types for full comprehension categories *)
Definition disp_bicat_of_unit_type_full_comp_cat
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_unit_type_comp_cat.

Definition univalent_2_1_disp_bicat_of_unit_type_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_unit_type_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_unit_type_comp_cat.
Qed.

Definition univalent_2_0_disp_bicat_of_unit_type_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_unit_type_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_unit_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_unit_type_comp_cat.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_unit_type_full_comp_cat
  : disp_univalent_2 disp_bicat_of_unit_type_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_unit_type_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_unit_type_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_unit_type_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_unit_type_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_unit_type_comp_cat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_unit_type_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_unit_type_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_unit_type_comp_cat.
Qed.

(** * 5. Adjoint equivalences *)
Definition disp_adjoint_equiv_disp_bicat_of_unit_type_full_comp_cat_help
           {C₁ C₂ : full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {T₁ : disp_bicat_of_unit_type_full_comp_cat C₁}
           {T₂ : disp_bicat_of_unit_type_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F T₁ T₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - intros C T₁ T₂ FF.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use disp_left_adjoint_equivalence_subbicat_alt.
    exact is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_unit_type_full_comp_cat
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_unit_type_full_comp_cat C₁}
           {T₂ : disp_bicat_of_unit_type_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_unit_type_full_comp_cat_help (F ,, HF) FF).
Defined.

(** * 6. Strong unit types *)
Definition disp_bicat_of_strong_unit_type
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : full_comp_cat),
            ∑ (T : fiberwise_terminal (cleaving_of_types C)),
            ∏ (Γ : C), is_z_isomorphism (π (pr1 (pr1 T Γ)))).
  - exact (λ (C₁ C₂ : full_comp_cat)
             T₁ T₂
             (F : full_comp_cat_functor C₁ C₂),
           ∏ (x : C₁),
           preserves_terminal
             (fiber_functor (comp_cat_type_functor F) x)).
  - abstract
      (intros C T x y Hy ;
       exact Hy).
  - abstract
      (intros C₁ C₂ C₃ T₁ T₂ T₃ F G HF HG x y Hy ;
       apply HG ;
       apply HF ;
       exact Hy).
Defined.

Definition univalent_2_1_disp_bicat_of_strong_unit_type
  : disp_univalent_2_1 disp_bicat_of_strong_unit_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  use impred ; intro.
  apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_0_disp_bicat_of_strong_unit_type
  : disp_univalent_2_0 disp_bicat_of_strong_unit_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    use isaproptotal2.
    + intro.
      use impred ; intro.
      apply isaprop_is_z_isomorphism.
    + intros.
      apply isaprop_fiberwise_terminal.
  - intros C₁ C₂ T₁ T₂ f.
    use impred ; intro.
    apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_disp_bicat_of_strong_unit_type
  : disp_univalent_2 disp_bicat_of_strong_unit_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_strong_unit_type.
  - exact univalent_2_1_disp_bicat_of_strong_unit_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_strong_unit_type
  : disp_2cells_isaprop disp_bicat_of_strong_unit_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_strong_unit_type
  : disp_locally_groupoid disp_bicat_of_strong_unit_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_strong_unit_type_help
           {C₁ C₂ : full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {T₁ : disp_bicat_of_strong_unit_type C₁}
           {T₂ : disp_bicat_of_strong_unit_type C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F T₁ T₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - intros C T₁ T₂ FF.
    use disp_left_adjoint_equivalence_subbicat_alt.
    exact is_univalent_2_bicat_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_strong_unit_type
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_strong_unit_type C₁}
           {T₂ : disp_bicat_of_strong_unit_type C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_strong_unit_type_help (F ,, HF) FF).
Defined.
