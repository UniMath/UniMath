(************************************************************************

 Equivalences for inserters

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Limits.Inserters.

Local Open Scope cat.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁              y₁
                        ---- g₁ ---->
     |                |               |
     |                |               |
     l₃      ≃        l₁     ≃        l₂
     |                |               |
     |                |               |
     V                V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₁              y₂
                        ---- g₂ ---->


  where the columns are adjoint equivalences and both rows are inserters cones.
  If the top row is an inserter, then so is the bottom row.

 *)
Section InserterEquivalence.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : i₁ · f₁ ==> i₁ · g₁}
          (cone₁ :=  make_inserter_cone p₁ i₁ α₁)
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : i₂ · f₂ ==> i₂ · g₂}
          (cone₂ :=  make_inserter_cone p₂ i₂ α₂)
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (Hlp : left_adjoint_equivalence lp)
          (γ₁ : invertible_2cell (lp · i₂) (i₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (H : has_inserter_ump cone₁)
          (pα : (_ ◃ α₂)
                • lassociator _ _ _
                • (γ₁ ▹ _)
                • rassociator _ _ _
                • (_ ◃ γ₃)
                • lassociator _ _ _
                =
                lassociator _ _ _
                • (γ₁ ▹ _)
                • rassociator _ _ _
                • (_ ◃ γ₂)
                • lassociator _ _ _
                • (α₁ ▹ _)).

  Let rx : x₂ --> x₁
    := left_adjoint_right_adjoint Hlx.
  Let ηx : invertible_2cell (id₁ _) (lx · rx)
    := left_equivalence_unit_iso Hlx.
  Let εx : invertible_2cell (rx · lx) (id₁ _)
    := left_equivalence_counit_iso Hlx.

  Let ry : y₂ --> y₁
    := left_adjoint_right_adjoint Hly.
  Let ηy : invertible_2cell (id₁ _) (ly · ry)
    := left_equivalence_unit_iso Hly.
  Let εy : invertible_2cell (ry · ly) (id₁ _)
    := left_equivalence_counit_iso Hly.

  Let rp : p₂ --> p₁
    := left_adjoint_right_adjoint Hlp.
  Let ηp : invertible_2cell (id₁ _) (lp · rp)
    := left_equivalence_unit_iso Hlp.
  Let εp : invertible_2cell (rp · lp) (id₁ _)
    := left_equivalence_counit_iso Hlp.

  Let γ₁' : invertible_2cell (rp · i₁) (i₂ · rx)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηx)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₁)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εp))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₂' : invertible_2cell (rx · f₁) (f₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₂)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₃' : invertible_2cell (rx · g₁) (g₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₃)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Section UMP1.
    Context (q : inserter_cone f₂ g₂).

    Let cell : inserter_cone_pr1 q · rx · f₁
               ==>
               inserter_cone_pr1 q · rx · g₁
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hly)
           (rassociator _ _ _
            • (_ ◃ γ₂ ^-1)
            • lassociator _ _ _
            • (rassociator _ _ _ ▹ _)
            • (_ ◃ εx ▹ _)
            • (runitor _ ▹ _)
            • inserter_cone_cell q
            • (rinvunitor _ ▹ _)
            • ((_ ◃ εx^-1) ▹ _)
            • (lassociator _ _ _ ▹ _)
            • rassociator _ _ _
            • (_ ◃ γ₃)
            • lassociator _ _ _).

    Let ι : q --> p₁
      := inserter_ump_mor H (inserter_cone_pr1 q · rx) cell.

    Definition has_inserter_ump_1_left_adjoint_equivalence_mor
      : q --> p₂
      := ι · lp.

    Definition has_inserter_ump_1_left_adjoint_equivalence_pr1
      : invertible_2cell
          (has_inserter_ump_1_left_adjoint_equivalence_mor · inserter_cone_pr1 cone₂)
          (inserter_cone_pr1 q)
      := comp_of_invertible_2cell
           (rassociator_invertible_2cell _ _ _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell _ γ₁)
              (comp_of_invertible_2cell
                 (lassociator_invertible_2cell _ _ _)
                 (comp_of_invertible_2cell
                    (rwhisker_of_invertible_2cell
                       _
                       (inserter_ump_mor_pr1 H _ _))
                    (comp_of_invertible_2cell
                       (rassociator_invertible_2cell _ _ _)
                       (comp_of_invertible_2cell
                          (lwhisker_of_invertible_2cell
                             _
                             εx)
                          (runitor_invertible_2cell _)))))).

    Definition has_inserter_ump_1_left_adjoint_equivalence_cell
      : (_ ◃ inserter_cone_cell cone₂)
        • lassociator _ _ _
        • (has_inserter_ump_1_left_adjoint_equivalence_pr1 ▹ _)
        =
        lassociator _ _ _
        • (has_inserter_ump_1_left_adjoint_equivalence_pr1 ▹ _)
        • inserter_cone_cell q.
    Proof.
      unfold has_inserter_ump_1_left_adjoint_equivalence_mor.
      cbn -[cell].
      rewrite <- !rwhisker_vcomp.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      assert (lp ◃ α₂
              =
              lassociator _ _ _
              • (γ₁ ▹ _)
              • rassociator _ _ _
              • (_ ◃ γ₂)
              • lassociator _ _ _
              • (α₁ ▹ _)
              • rassociator _ _ _
              • (_ ◃ γ₃^-1)
              • lassociator _ _ _
              • (γ₁^-1 ▹ _)
              • rassociator _ _ _)
        as H'.
      {
        do 5 (use vcomp_move_L_Mp ; [ is_iso | ]).
        exact pα.
      }
      rewrite H' ; clear H'.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 5 (use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ]).
      cbn -[cell].
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      assert (ι ◃ α₁
              =
              lassociator _ _ _
              • (inserter_ump_mor_pr1 H (inserter_cone_pr1 q · rx) cell ▹ _)
              • cell
              • ((inserter_ump_mor_pr1 H (inserter_cone_pr1 q · rx) cell)^-1 ▹ _)
              • rassociator _ _ _)
        as H'.
      {
        do 2 (use vcomp_move_L_Mp ; [ is_iso | ]).
        exact (inserter_ump_mor_cell H _ cell).
      }
      rewrite H' ; clear H'.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 10 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lassociator_lassociator.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite lassociator_rassociator.
          rewrite id2_rwhisker.
          rewrite id2_left.
          rewrite !vassocl.
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
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite lwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite lwhisker_id2.
          rewrite id2_rwhisker.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_lassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[cell].
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lassociator_lassociator.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite lassociator_rassociator.
          rewrite id2_rwhisker.
          rewrite id2_left.
          rewrite !vassocl.
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
      etrans.
      {
        do 4 apply maponpaths.
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
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite rwhisker_rwhisker.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply εx.
      }
      cbn -[cell].
      rewrite !vassocr.
      apply fully_faithful_1cell_inv_map_eq.
    Qed.
  End UMP1.

  Definition has_inserter_ump_1_left_adjoint_equivalence
    : has_inserter_ump_1 cone₂.
  Proof.
    intro q.
    use make_inserter_1cell.
    - exact (has_inserter_ump_1_left_adjoint_equivalence_mor q).
    - exact (has_inserter_ump_1_left_adjoint_equivalence_pr1 q).
    - exact (has_inserter_ump_1_left_adjoint_equivalence_cell q).
  Defined.

  Section UMP2.
    Context {c : B}
            {u₁ u₂ : c --> p₂}
            (ζ : u₁ · i₂ ==> u₂ · i₂)
            (p : rassociator _ _ _ • (u₁ ◃ α₂) • lassociator _ _ _ • (ζ ▹ g₂)
                 =
                 (ζ ▹ _) • rassociator _ _ _ • (_ ◃ α₂) • lassociator _ _ _).

    Let cell : u₁ · rp · inserter_cone_pr1 cone₁
               ==>
               u₂ · rp · inserter_cone_pr1 cone₁
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hlx)
           (rassociator _ _ _
            • (_ ◃ γ₁^-1)
            • lassociator _ _ _
            • (rassociator _ _ _ ▹ _)
            • ((_ ◃ εp) ▹ _)
            • (runitor _ ▹ _)
            • ζ
            • (rinvunitor _ ▹ _)
            • ((_ ◃ εp ^-1) ▹ _)
            • (lassociator _ _ _ ▹ _)
            • rassociator _ _ _
            • (_ ◃ γ₁)
            • lassociator _ _ _).

    Lemma has_inserter_ump_2_left_adjoint_equivalence_cell_path
      : rassociator _ _ _
        • (_ ◃ inserter_cone_cell cone₁)
        • lassociator _ _ _
        • (cell ▹ _)
        =
        (cell ▹ _)
        • rassociator _ _ _
        • (_ ◃ inserter_cone_cell cone₁)
        • lassociator _ _ _.
    Proof.
      rewrite !vassocl.
      use (adj_equiv_faithful Hly).
      rewrite <- !rwhisker_vcomp.
      use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      use (vcomp_rcancel (_ ◃ γ₃^-1)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite vcomp_whisker.
      use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (_ ◃ γ₂)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      cbn -[cell].
      cbn in p.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite inverse_pentagon_7.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rassociator_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite pentagon_6.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        rewrite !rwhisker_vcomp.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        assert (rassociator _ _ _
                • (_ ◃ γ₂)
                • lassociator _ _ _
                • (α₁ ▹ _)
                • rassociator _ _ _
                • (_ ◃ γ₃^-1)
                • lassociator _ _ _
                =
                (γ₁^-1 ▹ _)
                • rassociator _ _ _
                • (_ ◃ α₂)
                • lassociator _ _ _
                • (γ₁ ▹ g₂))
          as H'.
        {
          do 3 (use vcomp_move_R_Mp ; [ is_iso | ]).
          rewrite !vassocl.
          do 2 (use vcomp_move_L_pM ; [ is_iso | ]).
          cbn.
          rewrite !vassocr.
          exact (!pα).
        }
        rewrite !vassocr.
        rewrite H'.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker.
          rewrite !vassocl.
          rewrite !rwhisker_vcomp.
          apply idpath.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          rewrite lwhisker_hcomp.
          rewrite pentagon_2.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_5.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite inverse_pentagon_7.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rassociator_rassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !vassocr.
          do 2 apply maponpaths_2.
          rewrite rwhisker_hcomp.
          rewrite !vassocl.
          rewrite <- inverse_pentagon_5.
          rewrite <- lwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocl.
        etrans.
        {
          do 5 apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker.
          rewrite !vassocl.
          rewrite <- lassociator_lassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        do 2 apply maponpaths_2.
        apply maponpaths.
        assert (rassociator _ _ _
                • (_ ◃ γ₂)
                • lassociator _ _ _
                • (α₁ ▹ _)
                • rassociator _ _ _
                • (_ ◃ γ₃^-1)
                • lassociator _ _ _
                =
                (γ₁^-1 ▹ _)
                • rassociator _ _ _
                • (_ ◃ α₂)
                • lassociator _ _ _
                • (γ₁ ▹ _))
          as H'.
        {
          do 3 (use vcomp_move_R_Mp ; [ is_iso | ]).
          rewrite !vassocl.
          do 2 (use vcomp_move_L_pM ; [ is_iso | ]).
          cbn.
          rewrite !vassocr.
          exact (!pα).
        }
        exact H'.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite <- !lwhisker_vcomp.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 5 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker.
          rewrite !vassocl.
          rewrite rwhisker_vcomp.
          apply idpath.
        }
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !vassocr.
          etrans.
          {
            apply maponpaths_2.
            rewrite lwhisker_hcomp.
            rewrite pentagon_2.
            rewrite <- rwhisker_hcomp.
            apply idpath.
          }
          rewrite !vassocl.
          rewrite rwhisker_vcomp.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_lwhisker.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite !vassocl.
          rewrite <- inverse_pentagon_2.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply fully_faithful_1cell_inv_map_eq.
        }
        rewrite !vassocl.
        etrans.
        {
          do 12 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        etrans.
        {
          do 11 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite lwhisker_id2.
          apply id2_left.
        }
        rewrite rassociator_lassociator.
        rewrite id2_right.
        apply idpath.
      }
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 apply maponpaths.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply fully_faithful_1cell_inv_map_eq.
        }
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          refine (vassocr _ _ _ @ _).
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          refine (vassocr _ _ _ @ _).
          rewrite lwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite lwhisker_id2.
          rewrite id2_left.
          apply idpath.
        }
        refine (vassocr _ _ _ @ _).
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[εp].
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      do 3 apply maponpaths.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[εp].
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite p.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      apply idpath.
    Qed.

    Definition has_inserter_ump_2_left_adjoint_equivalence_cell
      : u₁ ==> u₂.
    Proof.
      refine (rinvunitor _
              • (_ ◃ εp^-1)
              • lassociator _ _ _
              • (inserter_ump_cell H cell _ ▹ _)
              • rassociator _ _ _
              • (_ ◃ εp)
              • runitor _).
      exact has_inserter_ump_2_left_adjoint_equivalence_cell_path.
    Defined.

    Definition has_inserter_ump_2_left_adjoint_equivalence_pr1
      : has_inserter_ump_2_left_adjoint_equivalence_cell ▹ i₂ = ζ.
    Proof.
      unfold has_inserter_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn -[εp cell].
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (_ ◃ γ₁^-1)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (inserter_ump_cell_pr1 H cell _).
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      cbn -[εp cell].
      rewrite !vassocr.
      apply fully_faithful_1cell_inv_map_eq.
    Qed.
  End UMP2.

  Definition has_inserter_ump_2_left_adjoint_equivalence
    : has_inserter_ump_2 cone₂.
  Proof.
    intros c u₁ u₂ ζ p.
    simple refine (_ ,, _).
    - exact (has_inserter_ump_2_left_adjoint_equivalence_cell ζ p).
    - exact (has_inserter_ump_2_left_adjoint_equivalence_pr1 ζ p).
  Defined.

  Definition has_inserter_ump_eq_left_adjoint_equivalence
    : has_inserter_ump_eq cone₂.
  Proof.
    intros c u₁ u₂ ζ p φ₁ φ₂ q₁ q₂.
    enough (φ₁ ▹ rp = φ₂ ▹ rp) as H'.
    {
      use (adj_equiv_faithful (inv_adjequiv (_ ,, Hlp))).
      exact H'.
    }
    use (inserter_ump_eq_alt H) ; cbn.
    - rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      apply idpath.
    - cbn in q₁, q₂.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !rwhisker_rwhisker.
      apply maponpaths_2.
      use (vcomp_lcancel (_ ◃ (γ₁')^-1)) ; [ is_iso | ].
      rewrite <- !vcomp_whisker.
      apply maponpaths_2.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite <- !rwhisker_rwhisker_alt.
      apply maponpaths_2.
      apply maponpaths.
      exact (q₁ @ !q₂).
  Qed.

  Definition has_inserter_ump_left_adjoint_equivalence
    : has_inserter_ump cone₂.
  Proof.
    refine (_ ,, _ ,, _).
    - exact has_inserter_ump_1_left_adjoint_equivalence.
    - exact has_inserter_ump_2_left_adjoint_equivalence.
    - exact has_inserter_ump_eq_left_adjoint_equivalence.
  Defined.
End InserterEquivalence.
