(*********************************************************************

 Cartesian 1-cells

 In this file, we show that if we have 2 cartesian 1-cells over some
 1-cell, then we have an adjoint equivalence between their domains.

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.

Local Open Scope cat.
Local Open Scope mor_disp.

Section AdjEquivBetweenCartesian.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB_2_1 : is_univalent_2_1 B).

  Section MapAndCellFromCartesians.
    Context {x y : B}
            {f : x --> y}
            {xx₁ xx₂ : D x}
            {yy : D y}
            (ff₁ : xx₁ -->[ f ] yy)
            {ff₂ : xx₂ -->[ f ] yy}
            (Hff₂ : cartesian_1cell D ff₂).

    Let ff' : xx₁ -->[ id₁ x · f ] yy
      := transport_along_inv_2cell
           HB_2_1
           (linvunitor_invertible_2cell f)
           ff₁.
    Let ℓ : lift_1cell_factor D ff₂ ff'
      := pr1 Hff₂ x xx₁ (id₁ _) ff'.

    Definition map_between_cartesian_1cell
      : xx₁ -->[ id₁ _ ] xx₂
      := ℓ.

    Definition map_between_cartesian_1cell_commute
      : disp_invertible_2cell
          (lunitor_invertible_2cell _)
          (map_between_cartesian_1cell ;; ff₂)
          ff₁.
    Proof.
      refine (transportf
                (λ z, disp_invertible_2cell z _ _)
                _
                (vcomp_disp_invertible
                   (pr2 ℓ)
                   (transport_along_inv_2cell_disp_invertible_2cell _ _ _))).
      abstract
        (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         cbn ;
         apply id2_left).
    Defined.
  End MapAndCellFromCartesians.

  Section InverseOfCartesians.
    Context {x y : B}
            {f : x --> y}
            {xx₁ xx₂ : D x}
            {yy : D y}
            {ff₁ : xx₁ -->[ f ] yy}
            (Hff₁ : cartesian_1cell D ff₁)
            {ff₂ : xx₂ -->[ f ] yy}
            (Hff₂ : cartesian_1cell D ff₂).

    Let l : xx₁ -->[ id₁ x] xx₂
      := map_between_cartesian_1cell ff₁ Hff₂.

    Let δl : disp_invertible_2cell
               (lunitor_invertible_2cell f)
               (l ;; ff₂)
               ff₁
      := map_between_cartesian_1cell_commute ff₁ Hff₂.

    Let r : xx₂ -->[ id₁ x] xx₁
      := map_between_cartesian_1cell ff₂ Hff₁.

    Let δr : disp_invertible_2cell
               (lunitor_invertible_2cell f)
               (r ;; ff₁)
               ff₂
      := map_between_cartesian_1cell_commute ff₂ Hff₁.

    Let gg₁ : xx₂ -->[ id₁ x · f ] yy
      := transport_along_inv_2cell
           HB_2_1
           (linvunitor_invertible_2cell f)
           ff₂.

    Let γ₁ : disp_invertible_2cell
               (inv_of_invertible_2cell (linvunitor_invertible_2cell f))
               gg₁
               ff₂
      := transport_along_inv_2cell_disp_invertible_2cell
           HB_2_1
           (linvunitor_invertible_2cell f)
           ff₂.

    Let gg₂ : xx₂ -->[ id₁ x · id₁ x · f ] yy
      := transport_along_inv_2cell
           HB_2_1
           (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (linvunitor_invertible_2cell _)
                 (linvunitor_invertible_2cell _))
              (lassociator_invertible_2cell _ _ _))
           ff₂.

    Let γ₂ : disp_invertible_2cell _ gg₂ ff₂
      := transport_along_inv_2cell_disp_invertible_2cell
           HB_2_1
           (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (linvunitor_invertible_2cell _)
                 (linvunitor_invertible_2cell _))
              (lassociator_invertible_2cell _ _ _))
           ff₂.

    Local Lemma first_lift_path
      : comp_of_invertible_2cell
          (lunitor_invertible_2cell f)
          (inv_of_invertible_2cell
             (inv_of_invertible_2cell
                (linvunitor_invertible_2cell f)))
        =
        id2_invertible_2cell (id₁ x · f).
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_is_invertible_2cell.
      }
      cbn.
      apply lunitor_linvunitor.
    Qed.

    Local Definition first_lift
      : lift_1cell_factor D ff₂ gg₁.
    Proof.
      refine (id_disp _ ,, _).
      exact (transportf
               (λ z, disp_invertible_2cell z _ _)
               first_lift_path
               (vcomp_disp_invertible
                  (disp_invertible_2cell_lunitor _)
                  (inverse_of_disp_invertible_2cell γ₁))).
    Defined.

    Local Lemma second_lift_path
      : comp_of_invertible_2cell
          (rassociator_invertible_2cell _ _ _)
          (comp_of_invertible_2cell
             (lwhisker_of_invertible_2cell _ (lunitor_invertible_2cell _))
             (comp_of_invertible_2cell
                (lunitor_invertible_2cell f)
                (inv_of_invertible_2cell
                   (inv_of_invertible_2cell
                      (comp_of_invertible_2cell
                         (comp_of_invertible_2cell
                            (linvunitor_invertible_2cell _)
                            (linvunitor_invertible_2cell _))
                         (lassociator_invertible_2cell (id₁ x) (id₁ x) f))))))
        =
        id2_invertible_2cell (id₁ x · id₁ x · f).
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_is_invertible_2cell.
      }
      cbn.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_linvunitor.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      rewrite !vassocl.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite rassociator_lassociator.
      rewrite id2_right.
      rewrite runitor_lunitor_identity.
      rewrite rwhisker_vcomp.
      rewrite lunitor_linvunitor.
      apply id2_rwhisker.
    Qed.

    Local Definition second_lift
      : lift_1cell_factor D ff₂ gg₂.
    Proof.
      refine (r ;; l ,, _).
      exact (transportf
               (λ z, disp_invertible_2cell z _ _)
               second_lift_path
               (vcomp_disp_invertible
                  (disp_invertible_2cell_rassociator _ _ _)
                  (vcomp_disp_invertible
                     (disp_invertible_2cell_lwhisker r δl)
                     (vcomp_disp_invertible
                        δr
                        (inverse_of_disp_invertible_2cell γ₂))))).
    Defined.

    Local Definition help_cell₁
      : gg₂ ==>[ lunitor (id₁ x) ▹ f] gg₁.
    Proof.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (γ₂ •• disp_inv_cell γ₁)).
      abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite lunitor_linvunitor ;
         rewrite id2_right ;
         rewrite <- lunitor_triangle ;
         rewrite !vassocr ;
         rewrite rassociator_lassociator ;
         apply id2_left).
    Defined.

    Let w₁ : lift_2cell_factor D ff₂ help_cell₁ second_lift first_lift
      := pr2 Hff₂ x xx₂ _ _ _ gg₁ (lunitor (id₁ x)) help_cell₁ second_lift first_lift.

    Definition disp_adj_equiv_between_cartesian_1cell_inv
      : r ;; l ==>[ lunitor _ ] id_disp _
      := w₁.

    Let ζ : r ;; l ==>[ lunitor _ ] id_disp _
      := disp_adj_equiv_between_cartesian_1cell_inv.

    Local Definition help_cell₂
      : gg₁ ==>[ linvunitor (id₁ x) ▹ f] gg₂.
    Proof.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (γ₁ •• disp_inv_cell γ₂)).
      abstract
        (cbn ;
         rewrite !vassocr ;
         rewrite lunitor_linvunitor ;
         rewrite id2_left ;
         rewrite rwhisker_hcomp ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite <- triangle_l_inv ;
         rewrite <- lwhisker_hcomp ;
         apply maponpaths_2 ;
         rewrite linvunitor_assoc ;
         rewrite lwhisker_hcomp ;
         rewrite triangle_r_inv ;
         rewrite <- rwhisker_hcomp ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         apply idpath).
    Defined.

    Let w₂ : lift_2cell_factor D ff₂ help_cell₂ first_lift second_lift
      := pr2 Hff₂ x xx₂ _ _ _ gg₂ (linvunitor (id₁ x)) help_cell₂ first_lift second_lift.

    Definition inv_of_disp_adj_equiv_between_cartesian_1cell_inv
      : id_disp _ ==>[ linvunitor _ ] r ;; l
      := w₂.

    Let ξ : id_disp _ ==>[ linvunitor _ ] r ;; l
      := inv_of_disp_adj_equiv_between_cartesian_1cell_inv.

    Local Definition help_inv_cell₁
      : gg₂ ==>[ id₂ _ ▹ f ] gg₂
      := transportb
           (λ z, _ ==>[ z ] _)
           (id2_rwhisker _ _)
           (disp_id2 _).

    Local Lemma disp_adj_equiv_between_cartesian_inv₁
      : ζ •• ξ
        =
        transportb
          (λ z, r ;; l ==>[ z ] r ;; l)
          (vcomp_rinv (is_invertible_2cell_lunitor (id₁ x)))
          (disp_id2 (r ;; l)).
    Proof.
      refine (!(transportbfinv (λ z, _ ==>[ z ] _) (lunitor_linvunitor _) _) @ _).
      refine (_ @ transportbfinv (λ z, _ ==>[ z ] _) (lunitor_linvunitor _) _).
      apply maponpaths.
      use (isaprop_lift_of_lift_2cell
             _ _
             (pr2 Hff₂ _ _ _ _ _ _ _ help_inv_cell₁ second_lift second_lift)).
      - rewrite disp_rwhisker_transport_left_new.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite disp_rwhisker_vcomp_alt.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite disp_vassocl.
        unfold transportb.
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          exact (eq_lift_2cell_alt _ _ w₂).
        }
        unfold transportb.
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        unfold help_cell₂.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
          apply maponpaths_2.
          exact (eq_lift_2cell_alt _ _ w₁).
        }
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        unfold help_cell₁.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite !disp_vassocl.
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 3 apply maponpaths.
          refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
          rewrite disp_vcomp_linv.
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite disp_id2_left.
          unfold transportb.
          rewrite transport_f_f.
          apply idpath.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply disp_vcomp_rinv.
        }
        unfold transportb.
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply disp_id2_right.
        }
        unfold transportb.
        rewrite transport_f_f.
        unfold help_inv_cell₁.
        unfold transportb.
        rewrite disp_mor_transportf_prewhisker.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply disp_id2_right.
        }
        unfold transportb.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
      - unfold help_inv_cell₁, transportb.
        rewrite !disp_rwhisker_transport_left_new.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite disp_id2_rwhisker.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite disp_id2_left, disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
    Qed.

    Local Definition help_inv_cell₂
      : gg₁ ==>[ id₂ (id₁ x) ▹ f ] gg₁
      := transportb
           (λ z, _ ==>[ z ] _)
           (id2_rwhisker _ _)
           (disp_id2 _).

    Local Lemma disp_adj_equiv_between_cartesian_inv₂
      : ξ •• ζ
        =
        transportb
          (λ z, id_disp xx₂ ==>[ z ] id_disp xx₂)
          (vcomp_linv (is_invertible_2cell_lunitor (id₁ x)))
          (disp_id2 (id_disp xx₂)).
    Proof.
      refine (!(transportbfinv (λ z, _ ==>[ z ] _) (linvunitor_lunitor _) _) @ _).
      refine (_ @ transportbfinv (λ z, _ ==>[ z ] _) (linvunitor_lunitor _) _).
      apply maponpaths.
      use (isaprop_lift_of_lift_2cell
             _ _
             (pr2 Hff₂ x _ _ _ _ _ _ help_inv_cell₂ first_lift first_lift)).
      - cbn.
        etrans.
        {
          do 2 apply maponpaths.
          exact (transportf_disp_invertible_2cell first_lift_path _).
        }
        cbn.
        rewrite disp_rwhisker_transport_left_new.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite disp_rwhisker_vcomp_alt.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (transportf_disp_invertible_2cell first_lift_path _).
        }
        cbn.
        rewrite disp_mor_transportf_postwhisker.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _) ; apply maponpaths.
          apply maponpaths.
          pose (maponpaths
                  (λ z, _ •• z)
                  (!(transportf_disp_invertible_2cell first_lift_path _))
                @ eq_lift_2cell_alt _ _ w₁) as p.
          cbn in p.
          rewrite disp_mor_transportf_prewhisker in p.
          pose (p' := @transportb_transpose_right
                        _ (λ z, _ ==>[ z ] _)
                        _ _ _ _ _
                        p).
          exact p'.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_2.
          exact (transportf_disp_invertible_2cell second_lift_path _).
        }
        cbn.
        rewrite disp_mor_transportf_postwhisker.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
          apply maponpaths_2.
          pose (maponpaths
                  (λ z, _ •• z)
                  (!(transportf_disp_invertible_2cell second_lift_path _))
                @ eq_lift_2cell_alt _ _ w₂) as p.
          cbn in p.
          rewrite disp_mor_transportf_prewhisker in p.
          pose (p' := @transportb_transpose_right
                        _ (λ z, _ ==>[ z ] _)
                        _ _ _ _ _
                        p).
          exact p'.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          exact (transportf_disp_invertible_2cell first_lift_path _).
        }
        cbn.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        unfold help_cell₂, help_cell₁.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite !disp_vassocl.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          refine (disp_vassocl _ _ _ @ _) ; apply maponpaths.
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
            apply maponpaths_2.
            exact (disp_vcomp_linv γ₁).
          }
          unfold transportb.
          rewrite !disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply disp_id2_left.
          }
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          apply maponpaths.
          refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (disp_vcomp_linv γ₂).
          }
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          apply maponpaths.
          apply disp_id2_left.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        unfold help_inv_cell₂.
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          apply disp_id2_right.
        }
        unfold transportb.
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
      - unfold help_inv_cell₂.
        unfold transportb.
        rewrite !disp_rwhisker_transport_left_new.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite disp_id2_rwhisker.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite disp_id2_left, disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
    Qed.

    Definition disp_adj_equiv_between_cartesian_1cell_inv_is_invertible
      : is_disp_invertible_2cell (is_invertible_2cell_lunitor _) ζ
      := ξ
         ,,
         disp_adj_equiv_between_cartesian_inv₁
         ,,
         disp_adj_equiv_between_cartesian_inv₂.

    Definition disp_adj_equiv_between_cartesian_1cell_inv_2cell
      : disp_invertible_2cell (lunitor_invertible_2cell _) (r ;; l) (id_disp _).
    Proof.
      refine (ζ ,, _).
      apply disp_adj_equiv_between_cartesian_1cell_inv_is_invertible.
    Defined.
  End InverseOfCartesians.

  Section DispAdjEquivBetweenCartesians.
    Context {x y : B}
            {f : x --> y}
            {xx₁ xx₂ : D x}
            {yy : D y}
            {ff₁ : xx₁ -->[ f ] yy}
            (Hff₁ : cartesian_1cell D ff₁)
            {ff₂ : xx₂ -->[ f ] yy}
            (Hff₂ : cartesian_1cell D ff₂).

    Let l : xx₁ -->[ id₁ x] xx₂
      := map_between_cartesian_1cell ff₁ Hff₂.
    Let r : xx₂ -->[ id₁ x] xx₁
      := map_between_cartesian_1cell ff₂ Hff₁.

    Local Definition disp_adj_equiv_between_cartesian_1cell_unit
      : id_disp _ ==>[ linvunitor _ ] l ;; r.
    Proof.
      exact (pr1 (inverse_of_disp_invertible_2cell
                    (disp_adj_equiv_between_cartesian_1cell_inv_2cell Hff₂ Hff₁))).
    Defined.

    Let η : id_disp _ ==>[ linvunitor _ ] l ;; r
      := disp_adj_equiv_between_cartesian_1cell_unit.

    Local Definition disp_adj_equiv_between_cartesian_1cell_unit_invertible
      : is_disp_invertible_2cell (is_invertible_2cell_linvunitor _) η.
    Proof.
      refine (transportf
                (λ z, is_disp_invertible_2cell z _)
                _
                (pr2 (inverse_of_disp_invertible_2cell
                        (disp_adj_equiv_between_cartesian_1cell_inv_2cell
                           Hff₂ Hff₁)))).
      apply isaprop_is_invertible_2cell.
    Defined.

    Local Definition disp_adj_equiv_between_cartesian_1cell_counit
      : r ;; l ==>[ lunitor _ ] id_disp _
      := disp_adj_equiv_between_cartesian_1cell_inv Hff₁ Hff₂.

    Let ε : r ;; l ==>[ lunitor _ ] id_disp _
      := disp_adj_equiv_between_cartesian_1cell_counit.

    Local Definition disp_adj_equiv_between_cartesian_1cell_counit_invertible
      : is_disp_invertible_2cell (is_invertible_2cell_lunitor (id₁ x)) ε
      := disp_adj_equiv_between_cartesian_1cell_inv_is_invertible Hff₁ Hff₂.

    Definition disp_adj_equiv_between_cartesian_1cell
      : ∑ (e : left_adjoint_equivalence (id₁ x)),
        disp_left_adjoint_equivalence e l.
    Proof.
      use disp_left_equivalence_to_left_adjoint_equivalence.
      - exact (left_equivalence_of_left_adjoint_equivalence
                 (internal_adjoint_equivalence_identity x)).
      - refine ((r ,, η ,, ε) ,, _ ,, _).
        + exact disp_adj_equiv_between_cartesian_1cell_unit_invertible.
        + exact disp_adj_equiv_between_cartesian_1cell_counit_invertible.
    Defined.
  End DispAdjEquivBetweenCartesians.
End AdjEquivBetweenCartesian.
