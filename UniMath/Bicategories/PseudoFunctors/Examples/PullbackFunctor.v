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
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.Colimits.PullbackFunctions.
Import PullbackFunctions.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.

Local Open Scope cat.

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
      apply invertible_2cell_in_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
      + is_iso.
    - intros.
      apply invertible_2cell_in_slice_bicat ; cbn.
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

Definition TODO {A : UU} : A.
Admitted.

Section DispMapPullbackFunctor.
  Context (B : bicat_with_pb)
          (D : disp_map_bicat B)
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

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
      + (*
          - pred_mor should be closed under invertible_2cells
          - invertible_2cells of pb_ump_mor
         *)
        cbn.
        unfold pb_on_1cell, mor_to_pb_obj.
        pose (pred_mor_closed_under_pb_ump_mor
                D
                _ _ _ _ _ _ _ _ _
                (mirror_has_pb_ump (pb_obj_has_pb_ump f (pr12 g₂)))
                _
                _
                _ _
                (id₁ _)
                TODO
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
        cbn in c.
        apply TODO.
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
      apply invertible_2cell_in_disp_map_slice_bicat ; cbn.
      use is_invertible_2cell_pb_ump_cell.
      + is_iso.
      + is_iso.
    - intros.
      apply invertible_2cell_in_disp_map_slice_bicat ; cbn.
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
