Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayMapBicat.

Local Open Scope cat.

Section DispMapSliceBicat.
  Context {B : bicat}
          (D : arrow_subbicat B)
          (b : B).

  Definition disp_map_slice_disp_cat_ob_mor
    : disp_cat_ob_mor B.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a, ∑ (f : a --> b), pred_ob D f).
    - exact (λ a₁ a₂ fa₁ fa₂ g,
             pred_mor D (pr1 fa₁) (pr1 fa₂) g
             ×
             invertible_2cell (pr1 fa₁) (g · pr1 fa₂)).
  Defined.

  Definition disp_map_slice_disp_cat_id_comp
    : disp_cat_id_comp B disp_map_slice_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ a fa,
             id_pred_mor D _
             ,,
             linvunitor_invertible_2cell (pr1 fa)).
    - exact (λ a₁ a₂ a₃ g₁ g₂ fa₁ fa₂ fa₃ α β,
             comp_pred_mor D (pr1 α) (pr1 β)
             ,,
             comp_of_invertible_2cell
               (pr2 α)
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     (pr2 β))
                  (lassociator_invertible_2cell _ _ _))).
  Defined.

  Definition disp_map_slice_disp_cat_data
    : disp_cat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_cat_ob_mor.
    - exact disp_map_slice_disp_cat_id_comp.
  Defined.

  Definition disp_map_slice_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_cat_data.
    - intros a₁ a₂ g₁ g₂ α fa₁ fa₂ β₁ β₂ ; cbn in *.
      exact (pr12 β₁ • (α ▹ _) = pr12 β₂).
  Defined.

  Definition disp_map_slice_disp_prebicat_ops
    : disp_prebicat_ops disp_map_slice_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split ; cbn.
    - intros.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intros.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      rewrite linvunitor_lunitor.
      apply id2_right.
    - intros.
      rewrite !vassocl.
      rewrite <- lunitor_lwhisker.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply id2_right.
    - intros.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ].
      use vcomp_move_R_Mp ; [ is_iso | ].
      cbn.
      rewrite lunitor_triangle.
      apply idpath.
    - intros.
      apply maponpaths.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite triangle_l_inv.
      apply idpath.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ].
      refine (!_).
      apply lassociator_lassociator.
    - intros.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply lassociator_lassociator.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? p q.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite p.
      exact q.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? p.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      exact p.
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? p.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      exact p.
  Qed.

  Definition disp_map_slice_disp_prebicat_data
    : disp_prebicat_data B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat_1_id_comp_cells.
    - exact disp_map_slice_disp_prebicat_ops.
  Defined.

  Definition disp_map_slice_disp_prebicat_laws
    : disp_prebicat_laws disp_map_slice_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply cellset_property.
  Qed.

  Definition disp_map_slice_disp_prebicat
    : disp_prebicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat_data.
    - exact disp_map_slice_disp_prebicat_laws.
  Defined.

  Definition disp_map_slice_disp_bicat
    : disp_bicat B.
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_slice_disp_prebicat.
    - cbn.
      intro ; intros.
      apply isasetaprop.
      apply cellset_property.
  Defined.

  Definition disp_2cells_isaprop_disp_map_slice
    : disp_2cells_isaprop disp_map_slice_disp_bicat.
  Proof.
    intro ; intros.
    apply cellset_property.
  Defined.

  Definition disp_locally_sym_disp_map_slice
    : disp_locally_sym disp_map_slice_disp_bicat.
  Proof.
    intros a₁ a₂ g₁ g₂ α fa₁ fa₂ β₁ β₂ p ; cbn in *.
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite vcomp_rinv.
    rewrite id2_rwhisker.
    apply id2_right.
  Qed.

  Definition disp_locally_groupoid_disp_map_slice_disp_bicat
    : disp_locally_groupoid disp_map_slice_disp_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_disp_map_slice.
    - exact disp_2cells_isaprop_disp_map_slice.
  Defined.
End DispMapSliceBicat.

Definition disp_map_slice_bicat
           {B : bicat}
           (D : arrow_subbicat B)
           (b : B)
  : bicat
  := total_bicat (disp_map_slice_disp_bicat D b).

Definition eq_2cell_disp_map_slice
           {B : bicat}
           {D : arrow_subbicat B}
           {b : B}
           {y₁ y₂ : disp_map_slice_bicat D b}
           {f g : y₁ --> y₂}
           {α β : f ==> g}
           (p : pr1 α = pr1 β)
  : α = β.
Proof.
  use subtypePath.
  {
    intro.
    apply cellset_property.
  }
  exact p.
Qed.

Definition invertible_2cell_in_disp_map_slice_bicat
           {B : bicat}
           {D : arrow_subbicat B}
           {b : B}
           {f₁ f₂ : disp_map_slice_bicat D b}
           {g₁ g₂ : f₁ --> f₂}
           {α : g₁ ==> g₂}
           (Hα : is_invertible_2cell (pr1 α))
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  simple refine (_ ,, _).
  - exact Hα.
  - apply (disp_locally_groupoid_disp_map_slice_disp_bicat
             _ _ _ _ _ _
             (make_invertible_2cell Hα)).
Defined.
