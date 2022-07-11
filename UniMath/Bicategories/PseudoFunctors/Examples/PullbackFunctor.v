(*************************************************************

 Pullback functors

 In this file, we look at the change of base functors arising
 from pullbacks. We look at two version:

 1. Change of base for slice bicategories
 2. Change of base for slices of display map bicategories
 3. Change of base in the discrete case

 *************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Import PullbackFunctions.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.

Local Open Scope cat.

(**
 1. Change of base for slice bicategories
 *)
Section PullbackFunctor.
  Context (B : bicat_with_pb)
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

  Definition pb_psfunctor_data
    : psfunctor_data
        (slice_bicat b₂)
        (slice_bicat b₁).
  Proof.
    use make_psfunctor_data.
    - exact (λ g, pb_obj f (pr2 g) ,, pb_pr1 f (pr2 g)).
    - simple refine (λ g₁ g₂ α, _ ,, _).
      + exact (f /≃₁ pr2 α).
      + exact (inv_of_invertible_2cell (pb_on_1cell_pr1 f (pr2 α))).
    - intros g₁ g₂ α β p.
      simple refine (_ ,, _).
      + exact (f /≃₂ pr2 p).
      + exact (pb_on_2cell_coh (pr2 α) (pr2 β) (pr1 p) (pr2 p)).
    - intro g.
      simple refine (_ ,, _).
      + exact (pb_1cell_on_id f (pr2 g)).
      + exact (pb_1cell_on_id_coh f (pr2 g)).
    - intros g₁ g₂ g₃ α β ; cbn.
      simple refine (_ ,, _).
      + exact (pb_1cell_on_comp f (pr2 α) (pr2 β)).
      + exact (pb_1cell_on_comp_coh f (pr2 α) (pr2 β)).
  Defined.

  Definition pb_psfunctor_laws
    : psfunctor_laws pb_psfunctor_data.
  Proof.
    repeat split.
    - intros g₁ g₂ α.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_id.
    - intros g₁ g₂ α β γ p q.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_comp.
    - intros g₁ g₂ α.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_lunitor.
    - intros g₁ g₂ α.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_runitor.
    - intros g₁ g₂ g₃ g₄ α β γ.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_lassociator.
    - intros g₁ g₂ g₃ α β₁ β₂ p.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_lwhisker.
    - intros g₁ g₂ g₃ α₁ α₂ β p.
      use eq_2cell_slice ; cbn.
      apply pb_2cell_on_rwhisker.
  Qed.

  Definition pb_psfunctor_invertible_cells
    : invertible_cells pb_psfunctor_data.
  Proof.
    split.
    - intro.
      apply is_invertible_2cell_in_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
      + is_iso.
    - intros.
      apply is_invertible_2cell_in_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
  Defined.

  Definition pb_psfunctor
    : psfunctor
        (slice_bicat b₂)
        (slice_bicat b₁).
  Proof.
    use make_psfunctor.
    - exact pb_psfunctor_data.
    - exact pb_psfunctor_laws.
    - exact pb_psfunctor_invertible_cells.
  Defined.
End PullbackFunctor.

(**
 2. Change of base for slices of display map bicategories
 *)
Section DispMapPullbackFunctor.
  Context (B : bicat_with_pb)
          (D : disp_map_bicat B)
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

  Section PredMor_for_PB_Mor.
    Context {g₁ g₂ : disp_map_slice_bicat D b₂}
            (α : g₁ --> g₂).

    Let γ : invertible_2cell
              ((π₂ : f /≃ pr12 g₁ --> pr1 g₁) · pr1 α · pr12 g₂)
              (π₁ · id₁ b₁ · f)
      := comp_of_invertible_2cell
           (rassociator_invertible_2cell _ _ _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (pr22 α)))
              (comp_of_invertible_2cell
                 (inv_of_invertible_2cell (pb_cell f (pr12 g₁)))
                 (rwhisker_of_invertible_2cell
                    _
                    (rinvunitor_invertible_2cell _)))).

    Definition help_pred_mor_pb_on_1cell
      : pb_ump_mor
          (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₂)))
          (make_pb_cone
             (f /≃ pr12 g₁)
             ((π₂ : B ⟦ f /≃ pr12 g₁, pr1 g₁ ⟧) · pr1 α)
             (π₁ · id₁ b₁)
             γ)
        ==>
        f /≃₁ pr22 α.
    Proof.
      use pb_ump_cell.
      - apply (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₂))).
      - exact (pb_ump_mor_pr2
                 (pb_obj_has_pb_ump f (pr12 g₂))
                 (mirror_cone (make_pb_cone (f /≃ pr12 g₁) (π₂ · pr1 α) (π₁ · id₁ b₁) γ))
               • (pb_on_1cell_pr2 _ _)^-1).
      - exact (pb_ump_mor_pr1
                 (pb_obj_has_pb_ump f (pr12 g₂))
                 (mirror_cone (make_pb_cone (f /≃ pr12 g₁) (π₂ · pr1 α) (π₁ · id₁ b₁) γ))
               • runitor _
               • (pb_on_1cell_pr1 _ _)^-1).
      - abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           refine (!_) ;
           etrans ;
           [ apply maponpaths_2 ;
             exact (pb_ump_mor_cell
                      (pb_obj_has_pb_ump f (pr12 g₂))
                      (mirror_cone
                         (make_pb_cone
                            (f /≃ pr12 g₁)
                            (π₂ · pr1 α)
                            (π₁ · id₁ b₁)
                            γ)))
           | ] ;
           rewrite !vassocl ;
           apply maponpaths ;
           etrans ;
           [ do 3 apply maponpaths ;
             rewrite !vassocr ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite !vassocl ;
             apply idpath
           | ] ;
           etrans ;
           [ do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             rewrite !vassocl ;
             apply idpath
           | ] ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ;
           cbn ;
           rewrite pb_on_1cell_cell ;
           rewrite !vassocl ;
           refine (!_) ;
           etrans ;
           [ do 3 apply maponpaths ;
             rewrite !vassocr ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite !vassocl ;
             apply idpath
           | ] ;
           etrans ;
           [ do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             rewrite !vassocl ;
             apply idpath
           | ];
           apply idpath).
    Defined.

    Definition pred_mor_pb_on_1cell
      : pred_mor D π₁ π₁ (f /≃₁ pr22 α).
    Proof.
      pose (pred_mor_closed_under_pb_ump_mor
              D
              _ _ _ _ _ _ _ _ _
              (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₂)))
              _
              _
              _ _
              (id₁ _)
              γ
              (pr22 g₂)
              (mor_of_pb_preserves_pred_ob
                 D
                 (pr22 g₂)
                 (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₂))))
              (comp_pred_mor
                 D
                 (mor_of_pb_preserves_pred_ob
                    D
                    (pr22 g₁)
                    (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₁))))
                 (pr12 α)))
        as c.
      use (invertible_pred_mor_3 _ _ c).
      use make_invertible_2cell.
      - apply help_pred_mor_pb_on_1cell.
      - use is_invertible_2cell_pb_ump_cell.
        + is_iso.
          apply property_from_invertible_2cell.
        + is_iso.
          apply property_from_invertible_2cell.
    Qed.
  End PredMor_for_PB_Mor.

  Definition disp_map_pb_psfunctor_data
    : psfunctor_data
        (disp_map_slice_bicat D b₂)
        (disp_map_slice_bicat D b₁).
  Proof.
    use make_psfunctor_data.
    - exact (λ g,
             pb_obj f (pr12 g)
             ,,
             pb_pr1 f (pr12 g)
             ,,
             pb_preserves_pred_ob
               D
               (pr22 g)
               (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g)))).
    - simple refine (λ g₁ g₂ α, _ ,, _ ,, _).
      + exact (f /≃₁ pr22 α).
      + apply pred_mor_pb_on_1cell.
      + exact (inv_of_invertible_2cell (pb_on_1cell_pr1 f (pr22 α))).
    - intros g₁ g₂ α β p.
      simple refine (_ ,, _).
      + exact (f /≃₂ pr2 p).
      + exact (pb_on_2cell_coh (pr22 α) (pr22 β) (pr1 p) (pr2 p)).
    - intro g.
      simple refine (_ ,, _).
      + exact (pb_1cell_on_id f (pr12 g)).
      + exact (pb_1cell_on_id_coh f (pr12 g)).
    - intros g₁ g₂ g₃ α β ; cbn.
      simple refine (_ ,, _).
      + exact (pb_1cell_on_comp f (pr22 α) (pr22 β)).
      + exact (pb_1cell_on_comp_coh f (pr22 α) (pr22 β)).
  Defined.

  Definition disp_map_pb_psfunctor_laws
    : psfunctor_laws disp_map_pb_psfunctor_data.
  Proof.
    repeat split.
    - intros g₁ g₂ α.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_id.
    - intros g₁ g₂ α β γ p q.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_comp.
    - intros g₁ g₂ α.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_lunitor.
    - intros g₁ g₂ α.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_runitor.
    - intros g₁ g₂ g₃ g₄ α β γ.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_lassociator.
    - intros g₁ g₂ g₃ α β₁ β₂ p.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_lwhisker.
    - intros g₁ g₂ g₃ α₁ α₂ β p.
      use eq_2cell_disp_map_slice ; cbn.
      apply pb_2cell_on_rwhisker.
  Qed.

  Definition disp_map_pb_psfunctor_invertible_cells
    : invertible_cells disp_map_pb_psfunctor_data.
  Proof.
    split.
    - intro.
      apply is_invertible_2cell_in_disp_map_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
      + is_iso.
    - intros.
      apply is_invertible_2cell_in_disp_map_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
  Defined.

  Definition disp_map_pb_psfunctor
    : psfunctor
        (disp_map_slice_bicat D b₂)
        (disp_map_slice_bicat D b₁).
  Proof.
    use make_psfunctor.
    - exact disp_map_pb_psfunctor_data.
    - exact disp_map_pb_psfunctor_laws.
    - exact disp_map_pb_psfunctor_invertible_cells.
  Defined.
End DispMapPullbackFunctor.

(**
 3. Change of base in the discrete case
 *)
Section DiscreteDispMapPullbackFunctor.
  Context (B : bicat_with_pb)
          (HB : is_univalent_2_1 B)
          (D : disp_map_bicat B)
          (HD₁ : arrow_subbicat_props D)
          (HD₂ : contained_in_discrete D)
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

  Definition discrete_disp_map_pb_functor_data
    : functor_data
        (discrete_disp_map_slice HB HD₁ HD₂ b₂)
        (discrete_disp_map_slice HB HD₁ HD₂ b₁).
  Proof.
    use make_functor_data.
    - exact (λ g, disp_map_pb_psfunctor B D f g).
    - exact (λ g₁ g₂ α, #(disp_map_pb_psfunctor B D f) α).
  Defined.

  Definition discrete_disp_map_pb_is_functor
    : is_functor discrete_disp_map_pb_functor_data.
  Proof.
    split.
    - intro g.
      refine (!_).
      apply isotoid_2_1.
      + apply is_univalent_2_1_disp_map_slice.
        * exact HB.
        * exact HD₁.
      + exact (psfunctor_id (disp_map_pb_psfunctor B D f) g).
    - intros g₁ g₂ g₃ α β.
      refine (!_).
      apply isotoid_2_1.
      + apply is_univalent_2_1_disp_map_slice.
        * exact HB.
        * exact HD₁.
      + exact (psfunctor_comp (disp_map_pb_psfunctor B D f) α β).
  Qed.

  Definition discrete_disp_map_pb_functor
    : discrete_disp_map_slice HB HD₁ HD₂ b₂
      ⟶
      discrete_disp_map_slice HB HD₁ HD₂ b₁.
  Proof.
    use make_functor.
    - exact discrete_disp_map_pb_functor_data.
    - exact discrete_disp_map_pb_is_functor.
  Defined.
End DiscreteDispMapPullbackFunctor.
