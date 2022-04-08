(************************************************************************
 Morphisms in the slice bicategory

 We give characterizations for properties of morphisms in the slice
 bictegory. These characterizations only hold when the bicategory is
 locally groupoidal. If the bicategory is not locally groupoidal, there
 still are conditions for proving these properties.
 Note that for esos, we assume that the bicategory is locally groupoidal,
 so that the fully faithful 1-cells are characterized correctly.

 Contents:
 1. Proving properties of morphisms in the slice bicategory
 1.1 Faithful 1-cells
 1.2 Fully faithful 1-cells
 1.3 Conservative 1-cells
 1.4 Discrete 1-cells
 1.5 Pseudomonic 1-cells
 2. Characterizations
 2.1 Faithful 1-cells
 2.2 Fully faithful 1-cells
 3. Constructing esos in slice bicategory

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Eso.

Local Open Scope cat.

(**
 1. Proving properties of morphisms in the slice bicategory
 *)
Section ToMorphismInSlice.
  Context {B : bicat}
          {b : B}
          {f₁ f₂ : slice_bicat b}
          (α : f₁ --> f₂).

  (**
   1.1 Faithful 1-cells
   *)
  Definition to_faithful_slice
             (Hα : faithful_1cell (pr1 α))
    : faithful_1cell α.
  Proof.
    intros g β₁ β₂ p₁ p₂ q.
    use eq_2cell_slice.
    apply Hα.
    exact (maponpaths pr1 q).
  Qed.

  (**
   1.2 Fully faithful 1-cells
   *)
  Definition to_fully_faithful_slice
             (Hα : fully_faithful_1cell (pr1 α))
    : fully_faithful_1cell α.
  Proof.
    use make_fully_faithful.
    - apply to_faithful_slice.
      exact (pr1 Hα).
    - intros g β₁ β₂ pf.
      simple refine ((_ ,, _) ,, _).
      + exact (fully_faithful_1cell_inv_map Hα (pr1 pf)).
      + abstract
          (cbn ;
           use (vcomp_rcancel (_ ◃ pr12 α)) ;
           [ is_iso ; apply property_from_invertible_2cell | ] ;
           rewrite !vassocl ;
           rewrite vcomp_whisker ;
           use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
           rewrite !vassocl ;
           rewrite <- rwhisker_rwhisker ;
           rewrite (fully_faithful_1cell_inv_map_eq Hα (pr1 pf)) ;
           refine (_ @ pr2 pf) ; cbn ;
           rewrite !vassocl ;
           apply idpath).
      + abstract
          (use eq_2cell_slice ; cbn ;
           apply (fully_faithful_1cell_inv_map_eq Hα (pr1 pf))).
  Defined.

  (**
   1.3 Conservative 1-cells
   *)
  Definition to_conservative_slice
             (Hα : conservative_1cell (pr1 α))
    : conservative_1cell α.
  Proof.
    intros g β₁ β₂ p Hp.
    apply is_invertible_2cell_in_slice_bicat.
    apply Hα.
    apply (from_is_invertible_2cell_in_slice_bicat Hp).
  Defined.

  (**
   1.4 Discrete 1-cells
   *)
  Definition to_discrete_slice
             (Hα : discrete_1cell (pr1 α))
    : discrete_1cell α.
  Proof.
    split.
    - apply to_faithful_slice.
      exact (pr1 Hα).
    - apply to_conservative_slice.
      exact (pr2 Hα).
  Defined.

  (**
   1.5 Pseudomonic 1-cells
   *)
  Definition to_pseudomonic_slice
             (Hα : pseudomonic_1cell (pr1 α))
    : pseudomonic_1cell α.
  Proof.
    use make_pseudomonic.
    - apply to_faithful_slice.
      exact (pr1 Hα).
    - intros g β₁ β₂ pf Hpf.
      simple refine ((_ ,, _) ,, _ ,, _).
      + refine (pseudomonic_1cell_inv_map Hα (pr1 pf) _).
        exact (from_is_invertible_2cell_in_slice_bicat Hpf).
      + abstract
          (cbn ;
           use (vcomp_rcancel (_ ◃ pr12 α)) ;
           [ is_iso ; apply property_from_invertible_2cell | ] ;
           rewrite !vassocl ;
           rewrite vcomp_whisker ;
           use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
           rewrite !vassocl ;
           rewrite <- rwhisker_rwhisker ;
           rewrite (pseudomonic_1cell_inv_map_eq Hα (pr1 pf)) ;
           refine (_ @ pr2 pf) ; cbn ;
           rewrite !vassocl ;
           apply idpath).
      + use is_invertible_2cell_in_slice_bicat.
        cbn.
        apply is_invertible_2cell_pseudomonic_1cell_inv_map.
      + abstract
          (use eq_2cell_slice ; cbn ;
           apply (pseudomonic_1cell_inv_map_eq Hα (pr1 pf))).
  Defined.
End ToMorphismInSlice.

(**
 2. Characterizations
 *)
Section FromMorphismInSlice.
  Context {B : bicat}
          (inv_B : locally_groupoid B)
          {b : B}
          {f₁ f₂ : slice_bicat b}
          (α : f₁ --> f₂).

  (**
   2.1. Faithful 1-cells
   *)
  Definition from_faithful_slice
             (Hα : faithful_1cell α)
    : faithful_1cell (pr1 α).
  Proof.
    intros x g₁ g₂ α₁ α₂ p.
    pose (f₀ := make_ob_slice (g₁ · pr2 f₁)).
    pose (β₁ := @make_1cell_slice
                  _ _
                  f₀ f₁
                  g₁
                  (id2_invertible_2cell _)).
    pose (β₂ := @make_1cell_slice
                  _ _
                  f₀ f₁
                  g₂
                  (@make_invertible_2cell _ _ _ _ _ (α₁ ▹ _) (inv_B _ _ _ _ _))).
    assert (r₁ : cell_slice_homot β₁ β₂ α₁).
    {
      unfold cell_slice_homot.
      cbn.
      rewrite id2_left.
      apply idpath.
    }
    pose (p₁ := @make_2cell_slice _ _ _ _ β₁ β₂ α₁ r₁).
    assert (r₂ : cell_slice_homot β₁ β₂ α₂).
    {
      unfold cell_slice_homot.
      cbn.
      rewrite id2_left.
      use (vcomp_rcancel (_ ◃ pr12 α)) ; [ is_iso ; apply property_from_invertible_2cell | ].
      rewrite !vcomp_whisker.
      apply maponpaths.
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- !rwhisker_rwhisker.
      do 2 apply maponpaths.
      exact (!p).
    }
    pose (p₂ := @make_2cell_slice _ _ _ _ β₁ β₂ α₂ r₂).
    assert (r : p₁ ▹ α = p₂ ▹ α).
    {
      use eq_2cell_slice ; cbn.
      exact p.
    }
    exact (maponpaths pr1 (Hα f₀ β₁ β₂ p₁ p₂ r)).
  Qed.

  Definition faithful_weq_slice
    : faithful_1cell (pr1 α) ≃ faithful_1cell α.
  Proof.
    use weqimplimpl.
    - apply to_faithful_slice.
    - apply from_faithful_slice.
    - apply isaprop_faithful_1cell.
    - apply isaprop_faithful_1cell.
  Qed.

  (**
   2.2 Fully faithful 1-cells
   *)
  Section FromFullyFaithfulSlice.
    Context (Hα : fully_faithful_1cell α)
            {x : B}
            {g₁ g₂ : x --> pr1 f₁}
            (βf : g₁ · pr1 α ==> g₂ · pr1 α).

    Let h : slice_bicat b
      := make_ob_slice (g₁ · pr2 f₁).
    Let β₁ : h --> f₁
      := @make_1cell_slice _ _ h f₁ g₁ (id2_invertible_2cell _).
    Let γ : invertible_2cell (g₁ · pr2 f₁) (g₂ · pr2 f₁).
    Proof.
      use make_invertible_2cell.
      - exact ((_ ◃ pr12 α)
               • lassociator _ _ _
               • (βf ▹ _)
               • rassociator _ _ _
               • (_ ◃ (pr22 α)^-1)).
      - apply inv_B.
    Defined.
    Let β₂ : h --> f₁
      := @make_1cell_slice _ _ h f₁ g₂ γ.

    Local Lemma from_fully_faithful_slice_cell_homot
      : cell_slice_homot (β₁ · α) (β₂ · α) βf.
    Proof.
      unfold cell_slice_homot ; cbn.
      rewrite id2_left.
      rewrite !vassocl.
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_left.
      }
      rewrite rassociator_lassociator.
      apply id2_right.
    Qed.

    Let p : β₁ · α ==> β₂ · α
      := @make_2cell_slice
           _ _ _ _
           (β₁ · α) (β₂ · α)
           βf
           from_fully_faithful_slice_cell_homot.

    Definition from_fully_faithful_slice_cell
      : g₁ ==> g₂
      := pr1 (@fully_faithful_1cell_inv_map _ _ _ _ Hα h β₁ β₂ p).

    Definition from_fully_faithful_slice_cell_eq
      : from_fully_faithful_slice_cell ▹ pr1 α = βf
      := maponpaths pr1 (@fully_faithful_1cell_inv_map_eq _ _ _ _ Hα h β₁ β₂ p).
  End FromFullyFaithfulSlice.

  Definition from_fully_faithful_slice
             (Hα : fully_faithful_1cell α)
    : fully_faithful_1cell (pr1 α).
  Proof.
    use make_fully_faithful.
    - apply from_faithful_slice.
      exact (pr1 Hα).
    - intros x g₁ g₂ βf.
      simple refine (_ ,, _).
      + exact (from_fully_faithful_slice_cell Hα βf).
      + exact (from_fully_faithful_slice_cell_eq Hα βf).
  Defined.

  Definition fully_faithful_weq_slice
    : fully_faithful_1cell (pr1 α) ≃ fully_faithful_1cell α.
  Proof.
    use weqimplimpl.
    - apply to_fully_faithful_slice.
    - apply from_fully_faithful_slice.
    - apply isaprop_fully_faithful_1cell.
    - apply isaprop_fully_faithful_1cell.
  Qed.
End FromMorphismInSlice.

Section EsoSlice.
  Context {B : bicat}
          (HB : is_univalent_2_1 B)
          (inv_B : locally_groupoid B)
          {b : B}
          {f₁ f₂ : slice_bicat b}
          (α : f₁ --> f₂).

  (**
   3. Constructing esos in slice bicategory
   *)
  Section ToSliceEsoFull.
    Context (Hα : is_eso (pr1 α))
            {h₁ h₂ : slice_bicat b}
            {μ : h₁ --> h₂}
            (Hμ : fully_faithful_1cell μ)
            {β₁ β₂ : f₂ --> h₁}
            (p₁ : α · β₁ ==> α · β₂)
            (p₂ : β₁ · μ ==> β₂ · μ)
            (r : (p₁ ▹ μ) • rassociator α β₂ μ
                 =
                 rassociator α β₁ μ • (α ◃ p₂)).

    Definition to_eso_slice_lift_2_eq
      : cell_slice_homot
          β₁ β₂
          (is_eso_lift_2
             (pr1 α) Hα
             (from_fully_faithful_slice inv_B μ Hμ)
             (pr1 β₁) (pr1 β₂)
             (pr1 p₁) (pr1 p₂)
             (maponpaths pr1 r)).
    Proof.
      unfold cell_slice_homot.
      use (vcomp_rcancel (_ ◃ pr12 μ)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      rewrite !vassocl.
      rewrite vcomp_whisker.
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker.
      etrans.
      {
        do 4 apply maponpaths.
        apply is_eso_lift_2_right.
      }
      pose (r' := pr2 p₂).
      cbn in r'.
      rewrite !vassocl in r'.
      exact r'.
    Qed.

    Definition to_eso_slice_lift_2
      : β₁ ==> β₂.
    Proof.
      use make_2cell_slice.
      - exact (is_eso_lift_2
                 _
                 Hα
                 (from_fully_faithful_slice inv_B _ Hμ)
                 (pr1 β₁) (pr1 β₂)
                 (pr1 p₁) (pr1 p₂)
                 (maponpaths pr1 r)).
      - exact to_eso_slice_lift_2_eq.
    Defined.

    Definition to_eso_slice_lift_2_left
      : α ◃ to_eso_slice_lift_2 = p₁.
    Proof.
      use eq_2cell_slice.
      apply is_eso_lift_2_left.
    Qed.

    Definition to_eso_slice_lift_2_right
      : to_eso_slice_lift_2 ▹ μ = p₂.
    Proof.
      use eq_2cell_slice.
      apply is_eso_lift_2_right.
    Qed.
  End ToSliceEsoFull.

  Definition to_eso_full_slice
             (Hα : is_eso (pr1 α))
    : is_eso_full α
    := λ h₁ h₂ μ Hμ β₁ β₂ p₁ p₂ r,
       to_eso_slice_lift_2 Hα Hμ p₁ p₂ r
       ,,
       to_eso_slice_lift_2_left Hα Hμ p₁ p₂ r
       ,,
       to_eso_slice_lift_2_right Hα Hμ p₁ p₂ r.

  Definition to_eso_faithful_slice
             (Hα : is_eso (pr1 α))
    : is_eso_faithful α.
  Proof.
    intros h₁ h₂ μ Hμ β₁ β₂ p₁ p₂ r₁ r₂.
    use eq_2cell_slice.
    use (is_eso_lift_eq _ Hα (from_fully_faithful_slice inv_B _ Hμ)).
    - exact (maponpaths pr1 r₁).
    - exact (maponpaths pr1 r₂).
  Qed.

  Section ToSliceEsoEssentiallySurjective.
    Context (Hα : is_eso (pr1 α))
            {g₁ g₂ : slice_bicat b}
            {μ : g₁ --> g₂}
            (Hμ : fully_faithful_1cell μ)
            {β₁ : f₁ --> g₁}
            {β₂ : f₂ --> g₂}
            (p : invertible_2cell (β₁ · μ) (α · β₂)).

    Let γ : invertible_2cell (pr1 β₁ · pr1 μ) (pr1 α · pr1 β₂).
    Proof.
      use make_invertible_2cell.
      - exact (pr11 p).
      - apply inv_B.
    Defined.

    Definition to_eso_slice_lift_1
      : f₂ --> g₁.
    Proof.
      simple refine (_ ,, _).
      - exact (is_eso_lift_1
                 _ Hα
                 (from_fully_faithful_slice inv_B _ Hμ)
                 (pr1 β₁) (pr1 β₂)
                 γ).
      - pose (is_eso_lift_1_comm_right
                _ Hα
                (from_fully_faithful_slice inv_B _ Hμ)
                (pr1 β₁) (pr1 β₂)
                γ)
          as i.
        use make_invertible_2cell.
        + exact (pr12 β₂
                 • (i^-1 ▹ _)
                 • rassociator _ _ _
                 • (_ ◃ (pr22 μ)^-1)).
        + apply inv_B.
    Defined.

    Definition to_eso_slice_lift_1_left_eq
      : cell_slice_homot
          (α · to_eso_slice_lift_1)
          β₁
          (is_eso_lift_1_comm_left
             (pr1 α) Hα
             (from_fully_faithful_slice inv_B μ Hμ)
             (pr1 β₁) (pr1 β₂)
             γ).
    Proof.
      unfold cell_slice_homot.
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ].
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite !vassocl.
      pose (is_eso_lift_1_eq
              _ Hα
              (from_fully_faithful_slice inv_B _ Hμ)
              (pr1 β₁) (pr1 β₂)
              γ)
        as H.
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left] in H.
      use vcomp_move_R_pM ; [ apply property_from_invertible_2cell | ].
      use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ].
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_5.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite <- H.
      rewrite !vassocl.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker_alt.
      apply maponpaths.
      clear H.
      pose (pr21 p) as H.
      cbn in H.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ].
      use vcomp_move_L_Mp ; [ apply property_from_invertible_2cell | ].
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        rewrite !vassocl in H.
        exact H.
      }
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_right.
    Qed.

    Definition to_eso_slice_lift_1_left
      : invertible_2cell
          (α · to_eso_slice_lift_1)
          β₁.
    Proof.
      use make_invertible_2cell.
      - use make_2cell_slice.
        + exact (is_eso_lift_1_comm_left
                   _ Hα
                   (from_fully_faithful_slice inv_B _ Hμ)
                   (pr1 β₁) (pr1 β₂)
                   γ).
        + exact to_eso_slice_lift_1_left_eq.
      - apply is_invertible_2cell_in_slice_bicat.
        apply inv_B.
    Defined.

    Definition to_eso_slice_lift_1_right_eq
      : cell_slice_homot
          (to_eso_slice_lift_1 · μ)
          β₂
          (is_eso_lift_1_comm_right
             (pr1 α) Hα
             (from_fully_faithful_slice inv_B μ Hμ)
             (pr1 β₁) (pr1 β₂)
             γ).
    Proof.
      unfold cell_slice_homot.
      cbn -[is_eso_lift_1_comm_right is_eso_lift_1_comm_left].
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_right.
    Qed.

    Definition to_eso_slice_lift_1_right
      : invertible_2cell (to_eso_slice_lift_1 · μ) β₂.
    Proof.
      use make_invertible_2cell.
      - use make_2cell_slice.
        + exact (is_eso_lift_1_comm_right
                   _ Hα
                   (from_fully_faithful_slice inv_B _ Hμ)
                   (pr1 β₁) (pr1 β₂)
                   γ).
        + exact to_eso_slice_lift_1_right_eq.
      - apply is_invertible_2cell_in_slice_bicat.
        apply inv_B.
    Defined.

    Definition to_eso_slice_lift_1_eq
      : (to_eso_slice_lift_1_left ▹ μ) • p
        =
        rassociator _ _ _ • (α ◃ to_eso_slice_lift_1_right).
    Proof.
      use eq_2cell_slice.
      apply is_eso_lift_1_eq.
    Qed.
  End ToSliceEsoEssentiallySurjective.

  Definition to_eso_essentially_surjective_slice
             (Hα : is_eso (pr1 α))
    : is_eso_essentially_surjective α
    := λ g₁ g₂ μ Hμ β₁ β₂ p,
       to_eso_slice_lift_1 Hα Hμ p
       ,,
       to_eso_slice_lift_1_left Hα Hμ p
       ,,
       to_eso_slice_lift_1_right Hα Hμ p
       ,,
       to_eso_slice_lift_1_eq Hα Hμ p.

  Definition to_eso_slice
             (Hα : is_eso (pr1 α))
    : is_eso α.
  Proof.
    use make_is_eso.
    - use is_univalent_2_1_slice_bicat.
      exact HB.
    - exact (to_eso_full_slice Hα).
    - exact (to_eso_faithful_slice Hα).
    - exact (to_eso_essentially_surjective_slice Hα).
  Defined.
End EsoSlice.
