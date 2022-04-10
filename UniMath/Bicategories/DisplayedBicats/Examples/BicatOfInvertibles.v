(*************************************************************************

 Bicat of invertible 2-cells

 This is the bicategory where we only consider the invertible 2-cells.

 Contents
 1. Definition
 2. Univalence

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section BicatOfInv2Cells.
  Context (B : bicat).

  (**
   1. Definition
   *)
  Definition disp_prebicat_1_id_comp_cells_of_inv2cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (((_ ,, _) ,, (_ ,, _)) ,, _).
    - exact (λ _, unit).
    - exact (λ _ _ _ _ _, unit).
    - exact (λ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
    - exact (λ x y f g α _ _ _ _, is_invertible_2cell α).
  Defined.

  Definition disp_prebicat_ops_of_inv2cells
    : disp_prebicat_ops disp_prebicat_1_id_comp_cells_of_inv2cells.
  Proof.
    repeat split ; intro ; intros ; cbn ; is_iso.
  Defined.

  Definition disp_prebicat_data_of_inv2cells
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_1_id_comp_cells_of_inv2cells.
    - exact disp_prebicat_ops_of_inv2cells.
  Defined.

  Definition disp_prebicat_laws_of_inv2cells
    : disp_prebicat_laws disp_prebicat_data_of_inv2cells.
  Proof.
    repeat split ; intro ; intros ; apply isaprop_is_invertible_2cell.
  Qed.

  Definition disp_prebicat_of_inv2cells
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_data_of_inv2cells.
    - exact disp_prebicat_laws_of_inv2cells.
  Defined.

  Definition disp_bicat_of_inv2cells
    : disp_bicat B.
  Proof.
    refine (disp_prebicat_of_inv2cells ,, _).
    intro ; intros.
    apply isasetaprop.
    apply isaprop_is_invertible_2cell.
  Defined.

  Definition disp_bicat_of_inv2cells_disp_2cells_isaprop
    : disp_2cells_isaprop disp_bicat_of_inv2cells.
  Proof.
    intro ; intros.
    apply isaprop_is_invertible_2cell.
  Qed.

  Definition disp_bicat_of_inv2cells_locally_groupoid
    : disp_locally_groupoid disp_bicat_of_inv2cells.
  Proof.
    use make_disp_locally_groupoid.
    - intro ; intros.
      cbn in *.
      is_iso.
    - exact disp_bicat_of_inv2cells_disp_2cells_isaprop.
  Defined.

  (**
   2. Univalence
   *)
  Definition disp_univalent_2_1_disp_bicat_of_inv2cells
    : disp_univalent_2_1 disp_bicat_of_inv2cells.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intro ; intros.
    use isweqimplimpl.
    - intro.
      apply isapropunit.
    - apply isasetunit.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isaprop_is_disp_invertible_2cell.
      }
      apply disp_bicat_of_inv2cells_disp_2cells_isaprop.
  Qed.

  Definition disp_univalent_2_0_disp_bicat_of_inv2cells
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_bicat_of_inv2cells.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intro ; intros.
    use isweqimplimpl.
    - intro.
      apply isapropunit.
    - apply isasetunit.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        use (isaprop_disp_left_adjoint_equivalence _ _ HB_2_1).
        exact disp_univalent_2_1_disp_bicat_of_inv2cells.
      }
      apply isapropunit.
  Qed.

  Definition disp_univalent_2_disp_bicat_of_inv2cells
             (HB_2_1 : is_univalent_2_1 B)
    : disp_univalent_2 disp_bicat_of_inv2cells.
  Proof.
    split.
    - exact (disp_univalent_2_0_disp_bicat_of_inv2cells HB_2_1).
    - exact disp_univalent_2_1_disp_bicat_of_inv2cells.
  Qed.

  Definition bicat_of_inv2cells
    : bicat
    := total_bicat disp_bicat_of_inv2cells.

  Definition is_univalent_2_1_bicat_of_inv2cells
             (HB_2_1 : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_of_inv2cells.
  Proof.
    use total_is_univalent_2_1.
    - exact HB_2_1.
    - exact disp_univalent_2_1_disp_bicat_of_inv2cells.
  Defined.

  Definition is_univalent_2_0_bicat_of_inv2cells
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_0 : is_univalent_2_0 B)
    : is_univalent_2_0 bicat_of_inv2cells.
  Proof.
    use total_is_univalent_2_0.
    - exact HB_2_0.
    - use disp_univalent_2_0_disp_bicat_of_inv2cells.
      exact HB_2_1.
  Defined.

  Definition is_univalent_2_bicat_of_inv2cells
             (HB_2 : is_univalent_2 B)
    : is_univalent_2 bicat_of_inv2cells.
  Proof.
    use total_is_univalent_2.
    - apply disp_univalent_2_disp_bicat_of_inv2cells.
      exact (pr2 HB_2).
    - exact HB_2.
  Defined.

  Definition is_invertible_2cell_bicat_of_inv2cells
             {x y : bicat_of_inv2cells}
             {f g : x --> y}
             (α : f ==> g)
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - simple refine (_ ,, _).
      + exact ((pr2 α)^-1).
      + cbn.
        is_iso.
    - abstract
        (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply vcomp_rinv).
    - abstract
        (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply vcomp_linv).
  Defined.

  Definition locally_groupoid_bicat_of_inv2cells
    : locally_groupoid bicat_of_inv2cells.
  Proof.
    intro ; intros.
    apply is_invertible_2cell_bicat_of_inv2cells.
  Defined.

  Definition eq_2cell_bicat_of_inv2cells
             {x y : bicat_of_inv2cells}
             {f g : x --> y}
             {α β : f ==> g}
             (p : pr1 α = pr1 β)
    : α = β.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    exact p.
  Qed.
End BicatOfInv2Cells.
