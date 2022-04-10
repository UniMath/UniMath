(**************************************************************
 Composition

 We show that the pullback functor has a left biadjoint using
 universal arrows. The left biadjoint is given on objects by
 composition.

 Contents
 1. Action on objects
 2. The unit
 3. Fullness
 4. Faithfulness
 5. Essentially surjective
 6. Universal arrow
 **************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PullbackFunctor.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Import PullbackFunctions.Notations.

Local Open Scope cat.

Section Composition.
  Context {B : bicat_with_pb}
          (HB : is_univalent_2_1 B)
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

  (**
   1. Action on objects
   *)
  Definition comp_ob
    : slice_bicat b₁ → slice_bicat b₂
    := λ h, make_ob_slice (pr2 h · f).

  (**
   2. The unit
   *)
  Definition comp_unit_mor
             {x : B}
             (h : x --> b₁)
    : x --> f /≃ (h · f)
    := h ⊗[ linvunitor_invertible_2cell (h · f) ] (id₁ x).

  Definition comp_unit_inv2cell
             {x : B}
             (h : x --> b₁)
    : invertible_2cell
        h
        (comp_unit_mor h · pr2 (pb_psfunctor B f (comp_ob (make_ob_slice h))))
    := inv_of_invertible_2cell
         (mor_to_pb_obj_pr1
            h (id₁ x)
            (linvunitor_invertible_2cell (h · f))).

  Definition comp_unit
             (h : slice_bicat b₁)
    : h --> pb_psfunctor B f (comp_ob h).
  Proof.
    use make_1cell_slice.
    - exact (comp_unit_mor (pr2 h)).
    - exact (comp_unit_inv2cell (pr2 h)).
  Defined.

  (**
   3. Fullness
   *)
  Definition comp_full_cell
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α β : comp_ob h₁ --> h₂)
             (p : comp_unit h₁ · # (pb_psfunctor B f) α
                  ==>
                  comp_unit h₁ · # (pb_psfunctor B f) β)
    : pr1 α ==> pr1 β
    := linvunitor _
       • ((mor_to_pb_obj_pr2 _ _ _)^-1 ▹ _)
       • rassociator _ _ _
       • (_ ◃ (pb_on_1cell_pr2 f (pr2 α))^-1)
       • lassociator _ _ _
       • (pr1 p ▹ π₂)
       • rassociator _ _ _
       • (_ ◃ pb_on_1cell_pr2 _ _)
       • lassociator _ _ _
       • (mor_to_pb_obj_pr2 _ _ _ ▹ _)
       • lunitor _.

  Definition comp_full_homot
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α β : comp_ob h₁ --> h₂)
             (p : comp_unit h₁ · # (pb_psfunctor B f) α
                  ==>
                  comp_unit h₁ · # (pb_psfunctor B f) β)
    : cell_slice_homot α β (comp_full_cell α β p).
  Proof.
    unfold cell_slice_homot.
    unfold comp_full_cell.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    do 5 (use vcomp_move_R_Mp ; [ is_iso ; apply property_from_invertible_2cell | ]).
    cbn.
    use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite rwhisker_rwhisker_alt.
    use (vcomp_rcancel (_ ◃ (pb_cell _ _)^-1)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite vcomp_whisker.
    use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite <- rwhisker_rwhisker.
    assert (pr1 p ▹ π₁
            =
            rassociator _ _ _
            • (_ ◃ pb_on_1cell_pr1 f (pr2 α))
            • (_ ◃ (pb_on_1cell_pr1 f (pr2 β))^-1)
            • lassociator _ _ _)
      as H.
    {
      pose (pr2 p) as d.
      cbn in d.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ].
      cbn.
      use (vcomp_lcancel ((mor_to_pb_obj_pr1 _ _ _) ^-1)) ; [ is_iso | ].
      rewrite !vassocl in d.
      exact d.
    }
    etrans.
    {
      do 10 apply maponpaths.
      exact H.
    }
    clear H.
    refine (!_).
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite rwhisker_hcomp.
        rewrite inverse_pentagon_2.
        apply idpath.
      }
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      rewrite <- lassociator_lassociator.
      apply idpath.
    }
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    do 3 (use vcomp_move_R_Mp ; [ is_iso | ]) ; cbn.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 15 apply maponpaths.
      exact (pb_on_1cell_cell f (pr2 β)).
    }
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    {
      is_iso ; apply property_from_invertible_2cell.
    }
    cbn.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- rwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- rwhisker_lwhisker_rassociator.
    etrans.
    {
      do 8 apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite !vassocl.
      rewrite <- inverse_pentagon_4.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite rassociator_rassociator.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ].
    cbn.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 10 apply maponpaths.
      apply mor_to_pb_obj_cell.
    }
    rewrite !vassocl.
    rewrite lwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    do 7 (use vcomp_move_R_Mp ; [ is_iso ; apply property_from_invertible_2cell | ]).
    cbn.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 12 apply maponpaths.
      apply pb_on_1cell_cell.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- rwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 9 apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite vassocl.
      apply idpath.
    }
    rewrite <- lunitor_triangle.
    etrans.
    {
      do 4 apply maponpaths.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      apply idpath.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ].
    cbn.
    refine (!_).
    etrans.
    {
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_rassociator.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      apply idpath.
    }
    use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
    rewrite !vassocr.
    rewrite <- !vcomp_lunitor.
    rewrite <- !lunitor_triangle.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite vcomp_rinv.
    rewrite lwhisker_id2.
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      apply mor_to_pb_obj_cell.
    }
    rewrite !vassocl.
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      cbn.
      apply idpath.
    }
    rewrite linvunitor_assoc.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      apply id2_left.
    }
    rewrite !vassocr.
    rewrite lassociator_rassociator.
    apply id2_left.
  Qed.

  Definition comp_full
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α β : comp_ob h₁ --> h₂)
             (p : comp_unit h₁ · # (pb_psfunctor B f) α
                  ==>
                  comp_unit h₁ · # (pb_psfunctor B f) β)
    : α ==> β.
  Proof.
    use make_2cell_slice.
    - exact (comp_full_cell α β p).
    - exact (comp_full_homot α β p).
  Defined.

  Definition comp_full_eq
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α β : comp_ob h₁ --> h₂)
             (p : comp_unit h₁ · # (pb_psfunctor B f) α
                  ==>
                  comp_unit h₁ · # (pb_psfunctor B f) β)
    : comp_unit h₁ ◃ ## (pb_psfunctor B f) (comp_full α β p) = p.
  Proof.
    use eq_2cell_slice.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot ; cbn.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      }
      rewrite <- vcomp_whisker.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - cbn.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- rwhisker_lwhisker.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply pb_on_2cell_pr1.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ].
      cbn.
      use (vcomp_lcancel
             (mor_to_pb_obj_pr1
                (pr2 h₁) (id₁ _)
                (linvunitor_invertible_2cell _)^-1)).
      {
        is_iso.
      }
      rewrite !vassocr.
      refine (!_).
      pose (pr2 p) as p'.
      cbn in p'.
      rewrite !vassocr in p'.
      exact p'.
    - cbn.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- rwhisker_lwhisker.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply pb_on_2cell_pr2.
      }
      rewrite <- !lwhisker_vcomp.
      use vcomp_move_R_Mp ; [ is_iso | ].
      use vcomp_move_R_Mp ; [ is_iso | ].
      use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ].
      cbn.
      rewrite !vassocl.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      use (vcomp_lcancel ((mor_to_pb_obj_pr2 _ _ _)^-1 ▹ _)) ; [ is_iso | ].
      use (vcomp_rcancel (mor_to_pb_obj_pr2 _ _ _ ▹ _)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      use (vcomp_lcancel (linvunitor _)) ; [ is_iso | ].
      use (vcomp_rcancel (lunitor _)) ; [ is_iso | ].
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite vcomp_lunitor.
      etrans.
      {
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        apply id2_left.
      }
      rewrite !vassocr.
      apply idpath.
  Qed.

  (**
   4. Faithfulness
   *)
  Definition comp_faithful
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             {α β : comp_ob h₁ --> h₂}
             (p : comp_unit h₁ · # (pb_psfunctor B f) α
                  ==>
                  comp_unit h₁ · # (pb_psfunctor B f) β)
             (q₁ q₂ : α ==> β)
             (r₁ : comp_unit h₁ ◃ ## (pb_psfunctor B f) q₁ = p)
             (r₂ : comp_unit h₁ ◃ ## (pb_psfunctor B f) q₂ = p)
    : q₁ = q₂.
  Proof.
    use eq_2cell_slice.
    assert (comp_unit_mor (pr2 h₁) ◃ (π₂ ◃ pr1 q₁)
            =
            comp_unit_mor (pr2 h₁) ◃ (π₂ ◃ pr1 q₂))
      as H₁.
    {
      pose (H := maponpaths
                    (λ z, lassociator _ _ _ • (z ▹ π₂))
                    (maponpaths pr1 r₁ @ !(maponpaths pr1 r₂))).
      cbn in H.
      rewrite <- !rwhisker_lwhisker in H.
      rewrite !pb_on_2cell_pr2 in H.
      rewrite <- !lwhisker_vcomp in H.
      rewrite !vassocl in H.
      use (vcomp_lcancel (comp_unit_mor (pr2 h₁) ◃ pb_on_1cell_pr2 f (pr2 α))).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      use (vcomp_rcancel (comp_unit_mor (pr2 h₁) ◃ (pb_on_1cell_pr2 f (pr2 β)) ^-1)).
      {
        is_iso.
      }
      use (vcomp_rcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocl.
      exact H.
    }
    pose (maponpaths (λ z, rassociator _ _ _ • z • lassociator _ _ _) H₁) as H₂.
    cbn in H₂.
    rewrite !vassocl in H₂.
    rewrite !lwhisker_lwhisker in H₂.
    rewrite !vassocr in H₂.
    rewrite !rassociator_lassociator in H₂.
    rewrite !id2_left in H₂.
    unfold comp_unit_mor in H₂.
    pose (maponpaths (λ z, z • (mor_to_pb_obj_pr2 _ _ _ ▹ _)) H₂) as H₃.
    cbn in H₃.
    rewrite <- !vcomp_whisker in H₃.
    use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
    rewrite <- !vcomp_lunitor.
    apply maponpaths_2.
    use (vcomp_lcancel
           (mor_to_pb_obj_pr2 _ _ (linvunitor_invertible_2cell (pr2 h₁ · f)) ▹ _)).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    exact H₃.
  Qed.

  (**
   5. Essentially surjective
   *)
  Definition comp_essentially_surj_mor
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : pr1 h₁ --> pr1 h₂
    := pr1 α · π₂.

  Definition comp_essentially_surj_mor_inv2cell
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : invertible_2cell
        (pr2 h₁ · f)
        (comp_essentially_surj_mor α · pr2 h₂)
    := comp_of_invertible_2cell
         (rwhisker_of_invertible_2cell _ (pr2 α))
         (comp_of_invertible_2cell
            (rassociator_invertible_2cell _ _ _)
            (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell
                  _
                  (pb_cell _ _))
               (lassociator_invertible_2cell _ _ _))).

  Definition comp_essentially_surj
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : comp_ob h₁ --> h₂.
  Proof.
    use make_1cell_slice.
    - exact (comp_essentially_surj_mor α).
    - exact (comp_essentially_surj_mor_inv2cell α).
  Defined.

  Section EssentiallySurjective.
    Context {h₁ : slice_bicat b₁}
            {h₂ : slice_bicat b₂}
            (α : h₁ --> pb_psfunctor B f h₂).

    Local Arguments lassociator {_ _ _ _ _ _ _ _}.
    Local Arguments rassociator {_ _ _ _ _ _ _ _}.

    Definition comp_essentially_surj_cell_pr1
      : comp_unit_mor (pr2 h₁) · (f /≃₁ comp_essentially_surj_mor_inv2cell α) · π₁
        ==>
        pr1 α · π₁
      := rassociator
         • (_ ◃ pb_on_1cell_pr1 _ _)
         • mor_to_pb_obj_pr1 _ _ _
         • pr12 α.

    Definition comp_essentially_surj_cell_pr2
      : comp_unit_mor (pr2 h₁) · (f /≃₁ comp_essentially_surj_mor_inv2cell α) · π₂
        ==>
        pr1 α · π₂
      := rassociator
         • (_ ◃ pb_on_1cell_pr2 _ _)
         • lassociator
         • (mor_to_pb_obj_pr2 _ _ _ ▹ _)
         • lunitor _.

    Definition comp_essentially_surj_cell_eq
      : (_ ◃ pb_cone_cell _)
        • lassociator
        • (comp_essentially_surj_cell_pr2 ▹ _)
        • rassociator
        =
        lassociator
        • (comp_essentially_surj_cell_pr1 ▹ _)
        • rassociator
        • (pr1 α ◃ pb_cone_cell _).
    Proof.
      use (vcomp_lcancel lassociator) ; [ is_iso | ].
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths_2.
        apply maponpaths.
        apply pb_on_1cell_cell.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        unfold comp_unit_mor.
        apply mor_to_pb_obj_cell.
      }
      cbn.
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        do 9 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lassociator_lassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 11 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          unfold comp_essentially_surj_cell_pr2 .
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite <- !rwhisker_vcomp.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 10 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite !lwhisker_vcomp.
          rewrite lwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        apply id2_right.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_triangle.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      rewrite !vassocl.
      unfold comp_essentially_surj_cell_pr1.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    Qed.

    Definition comp_essentially_surj_cell
      : comp_unit_mor (pr2 h₁) · (f /≃₁ comp_essentially_surj_mor_inv2cell α)
        ==>
        pr1 α.
    Proof.
      use pb_ump_cell.
      - apply (pr2 B b₁ (pr1 h₂) b₂ f (pr2 h₂)).
      - exact comp_essentially_surj_cell_pr1.
      - exact comp_essentially_surj_cell_pr2.
      - exact comp_essentially_surj_cell_eq.
    Defined.
  End EssentiallySurjective.

  Definition comp_essentially_surj_cell_homot
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : cell_slice_homot
        (comp_unit h₁ · # (pb_psfunctor B f) (comp_essentially_surj α))
        α
        (comp_essentially_surj_cell α).
  Proof.
    unfold cell_slice_homot.
    cbn.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      apply pb_ump_cell_pr1.
    }
    unfold comp_essentially_surj_cell_pr1.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite vcomp_linv.
    apply id2_left.
  Qed.

  Definition comp_essentially_surj_cell_slice
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : comp_unit h₁ · # (pb_psfunctor B f) (comp_essentially_surj α)
      ==>
      α.
  Proof.
    use make_2cell_slice.
    - exact (comp_essentially_surj_cell α).
    - exact (comp_essentially_surj_cell_homot α).
  Defined.

  Definition comp_essentially_surj_is_inv2cell
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : is_invertible_2cell (comp_essentially_surj_cell_slice α).
  Proof.
    use is_invertible_2cell_in_slice_bicat.
    cbn.
    use is_invertible_2cell_pb_ump_cell.
    - unfold comp_essentially_surj_cell_pr1.
      is_iso.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
    - unfold comp_essentially_surj_cell_pr2.
      is_iso.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
  Defined.

  Definition comp_essentially_surj_inv2cell
             {h₁ : slice_bicat b₁}
             {h₂ : slice_bicat b₂}
             (α : h₁ --> pb_psfunctor B f h₂)
    : invertible_2cell
        (comp_unit h₁ · # (pb_psfunctor B f) (comp_essentially_surj α))
        α.
  Proof.
    use make_invertible_2cell.
    - exact (comp_essentially_surj_cell_slice α).
    - exact (comp_essentially_surj_is_inv2cell α).
  Defined.

  (**
   6. Universal arrow
   *)
  Definition pb_left_universal_arrow
    : left_universal_arrow (pb_psfunctor B f).
  Proof.
    use make_left_universal_arrow'.
    - use is_univalent_2_1_slice_bicat.
      exact HB.
    - exact comp_ob.
    - exact comp_unit.
    - exact (λ h₁ h₂ α β p,
             comp_full _ _ p ,, comp_full_eq _ _ p).
    - exact @comp_faithful.
    - exact (λ h₁ h₂ α, comp_essentially_surj α ,, comp_essentially_surj_inv2cell α).
  Defined.
End Composition.
