(*******************************************************************************************

 Comprehension categories with pi types

 In this file, we define the displayed bicategory of pi-types for comprehension categories,
 and we show that this displayed bicategory is univalent. We phrase pi-types by only referring
 to the fibration, and not to the comprehension structure, so this is a displayed bicategory
 over the bicategory of univalent categories with a fibration and a terminal object. In
 addition, note that we require the Beck-Chevalley condition even though this condition
 follows if the comprehension category has sigma types.

 Contents
 1. The displayed bicategory of pi-types
 2. The univalence of this displayed bicategory
 3. Pi-types for comprehension categories
 4. Pi-types for full comprehension categories
 5. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.

(** * 1. The displayed bicategory of pi-types *)
Proposition isaprop_dependent_product
            {C : cat_with_terminal_cleaving}
            {x y : C}
            (f : x --> y)
  : isaprop (dependent_product (cleaving_of_types C) f).
Proof.
  pose (D₁ := univalent_fiber_category (disp_cat_of_types C) y : bicat_of_univ_cats).
  pose (D₂ := univalent_fiber_category (disp_cat_of_types C) x : bicat_of_univ_cats).
  pose (F := (fiber_functor_from_cleaving _ (cleaving_of_types C) f : D₁ --> D₂)).
  use (isofhlevelweqf _ (left_adjoint_weq_is_left_adjoint F)).
  apply isaprop_left_adjoint.
  exact univalent_cat_is_univalent_2_1.
Qed.

Proposition isaprop_has_dependent_products
            (C : cat_with_terminal_cleaving)
  : isaprop (has_dependent_products (cleaving_of_types C)).
Proof.
  use isaproptotal2.
  - intro.
    do 10 (use impred ; intro).
    apply isaprop_right_beck_chevalley.
  - intros.
    do 3 (use funextsec ; intro).
    apply isaprop_dependent_product.
Qed.

Proposition preserves_dependent_products_id_cartesian
            (C : cat_with_terminal_cleaving)
            (P : has_dependent_products (cleaving_of_types C))
  : preserves_dependent_products (cartesian_comp_cat_type_functor (id₁ C)) P P.
Proof.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (id_preserves_dependent_products P)).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  apply idpath.
Qed.

Proposition preserves_dependent_products_comp_cartesian
            (C₁ C₂ C₃ : cat_with_terminal_cleaving)
            (P₁ : has_dependent_products (cleaving_of_types C₁))
            (P₂ : has_dependent_products (cleaving_of_types C₂))
            (P₃ : has_dependent_products (cleaving_of_types C₃))
            (F : functor_with_terminal_cleaving C₁ C₂)
            (G : functor_with_terminal_cleaving C₂ C₃)
            (HF : preserves_dependent_products
                    (cartesian_comp_cat_type_functor F)
                    P₁ P₂)
            (HG : preserves_dependent_products
                    (cartesian_comp_cat_type_functor G)
                    P₂ P₃)
  : preserves_dependent_products (cartesian_comp_cat_type_functor (F · G)) P₁ P₃.
Proof.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (comp_preserves_dependent_products HF HG)).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  apply idpath.
Qed.

Definition disp_bicat_of_pi_type
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat.
  - exact (λ (C : cat_with_terminal_cleaving),
           has_dependent_products (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : cat_with_terminal_cleaving)
             (P₁ : has_dependent_products (cleaving_of_types C₁))
             (P₂ : has_dependent_products (cleaving_of_types C₂))
             (F : functor_with_terminal_cleaving C₁ C₂),
           preserves_dependent_products (cartesian_comp_cat_type_functor F) P₁ P₂).
  - exact preserves_dependent_products_id_cartesian.
  - exact preserves_dependent_products_comp_cartesian.
Defined.

(** * 2. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_pi_type
  : disp_univalent_2_1 disp_bicat_of_pi_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ P₁ P₂ f.
  apply isaprop_preserves_dependent_products.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type
  : disp_univalent_2_0 disp_bicat_of_pi_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_with_terminal_cleaving.
  - intro C.
    apply isaprop_has_dependent_products.
  - intros C₁ C₂ P₁ P₂ f.
    apply isaprop_preserves_dependent_products.
Qed.

Definition univalent_2_disp_bicat_of_pi_type
  : disp_univalent_2 disp_bicat_of_pi_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type.
  - exact univalent_2_1_disp_bicat_of_pi_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type
  : disp_2cells_isaprop disp_bicat_of_pi_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type
  : disp_locally_groupoid disp_bicat_of_pi_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type
  : disp_2cells_iscontr disp_bicat_of_pi_type.
Proof.
  apply disp_2cells_iscontr_subbicat.
Qed.

(** * 3. Pi-types for comprehension categories *)
Definition disp_bicat_of_pi_type_comp_cat
  : disp_bicat bicat_comp_cat
  := lift_disp_bicat _ disp_bicat_of_pi_type.

Definition univalent_2_1_disp_bicat_of_pi_type_comp_cat
  : disp_univalent_2_1 disp_bicat_of_pi_type_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_pi_type.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type_comp_cat
  : disp_univalent_2_0 disp_bicat_of_pi_type_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_pi_type.
  - exact univalent_2_1_disp_bicat_of_pi_type.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_pi_type_comp_cat
  : disp_univalent_2 disp_bicat_of_pi_type_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type_comp_cat
  : disp_2cells_isaprop disp_bicat_of_pi_type_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_pi_type.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type_comp_cat
  : disp_locally_groupoid disp_bicat_of_pi_type_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_pi_type.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type_comp_cat
  : disp_2cells_iscontr disp_bicat_of_pi_type_comp_cat.
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  exact disp_2cells_iscontr_disp_bicat_of_pi_type.
Qed.

(** * 4. Pi-types for full comprehension categories *)
Definition disp_bicat_of_pi_type_full_comp_cat
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_pi_type_comp_cat.

Definition univalent_2_1_disp_bicat_of_pi_type_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_pi_type_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_pi_type_comp_cat.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_pi_type_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_pi_type_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_comp_cat.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_pi_type_full_comp_cat
  : disp_univalent_2 disp_bicat_of_pi_type_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_pi_type_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_pi_type_comp_cat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_pi_type_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_pi_type_comp_cat.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type_full_comp_cat
  : disp_2cells_iscontr disp_bicat_of_pi_type_full_comp_cat.
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  exact disp_2cells_iscontr_disp_bicat_of_pi_type_comp_cat.
Qed.

(** * 5. Pi-types for DFL full comprehension categories *)
Definition disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_bicat bicat_of_dfl_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_pi_type_full_comp_cat.

Definition univalent_2_1_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_pi_type_full_comp_cat.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_pi_type_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_full_comp_cat.
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_pi_type_full_comp_cat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_pi_type_full_comp_cat.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_2cells_iscontr disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  exact disp_2cells_iscontr_disp_bicat_of_pi_type_full_comp_cat.
Qed.

(** * 5. Adjoint equivalences *)
Definition disp_adjoint_equiv_disp_bicat_of_pi_type_help
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : adjoint_equivalence C₁ C₂)
           {P₁ : has_dependent_products (cleaving_of_types C₁)}
           {P₂ : has_dependent_products (cleaving_of_types C₂)}
  : preserves_dependent_products (cartesian_comp_cat_type_functor (pr1 F)) P₁ P₂.
Proof.
  revert C₁ C₂ F P₁ P₂.
  use J_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - intros C P₁ P₂.
    assert (P₁ = P₂) as p.
    {
      apply isaprop_has_dependent_products.
    }
    induction p.
    apply preserves_dependent_products_id_cartesian.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {P₁ : disp_bicat_of_pi_type_dfl_full_comp_cat C₁}
           {P₂ : disp_bicat_of_pi_type_dfl_full_comp_cat C₂}
           (FF : P₁ -->[ F ] P₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P₁ P₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  - intros C P₁ P₂ FF.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use disp_left_adjoint_equivalence_subbicat.
    + clear C P₁ P₂ FF.
      intros C₁ C₂ P₁ P₂ F HF.
      exact (disp_adjoint_equiv_disp_bicat_of_pi_type_help (F ,, HF)).
    + exact is_univalent_2_bicat_cat_with_terminal_cleaving.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_pi_type_dfl_full_comp_cat C₁}
           {T₂ : disp_bicat_of_pi_type_dfl_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat_help (F ,, HF) FF).
Defined.
