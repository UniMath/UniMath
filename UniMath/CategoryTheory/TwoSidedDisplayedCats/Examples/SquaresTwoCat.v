(**********************************************************************************

 Squares in a 2-category

 We define the 2-sided displayed category of squares in a 2-category. Here we require
 the squares to be given by 2-cells rather than equalities.

 In general this construction does not give rise to a univalent 2-sided displayed
 category even when we assume that the 2-category to be univalent. The reason for that
 the univalence of this 2-sided displayed category requires local univalence from the
 2-category. While this condition is not necessarily satisfied by univalent 2-categories,
 it is satisfied by, for example, categories enriched over posets.

 Contents
 1. Definition via two-sided displayed categories
 2. Univalence and strictness

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Import TwoCategories.Notations.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section TwoCatArrowTwoSidedDispCat.
  Context (C : two_cat).

  (** * 1. Definition via two-sided displayed categories *)
  Definition two_cat_arrow_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, x --> y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, h₁ · g ==> f · h₂).
  Defined.

  Definition two_cat_arrow_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp two_cat_arrow_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      exact (two_cat_runitor _ • two_cat_linvunitor _).
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ τ θ ; cbn in *.
      exact (two_cat_lassociator _ _ _
             • (τ ▹ _)
             • two_cat_rassociator _ _ _
             • (_ ◃ θ)
             • two_cat_lassociator _ _ _).
  Defined.

  Definition two_cat_arrow_twosided_disp_cat_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact two_cat_arrow_twosided_disp_cat_ob_mor.
    - exact two_cat_arrow_twosided_disp_cat_id_comp.
  Defined.

  Proposition transportb_disp_mor2_two_cat_arrow
              {x₁ x₂ y₁ y₂ : C}
              {f f' : x₁ --> x₂}
              (p : f' = f)
              {g g' : y₁ --> y₂}
              (q : g' = g)
              {h₁ : two_cat_arrow_twosided_disp_cat_data x₁ y₁}
              {h₂ : two_cat_arrow_twosided_disp_cat_data x₂ y₂}
              (τ : h₁ -->[ f ][ g ] h₂)
    : transportb_disp_mor2 p q τ
      =
      (_ ◃ idto2mor q) • τ • (idto2mor (!p) ▹ _).
  Proof.
    induction p, q.
    cbn.
    rewrite lwhisker_id2.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition transportf_disp_mor2_two_cat_arrow
              {x₁ x₂ y₁ y₂ : C}
              {f f' : x₁ --> x₂}
              (p : f = f')
              {g g' : y₁ --> y₂}
              (q : g = g')
              {h₁ : two_cat_arrow_twosided_disp_cat_data x₁ y₁}
              {h₂ : two_cat_arrow_twosided_disp_cat_data x₂ y₂}
              (τ : h₁ -->[ f ][ g ] h₂)
    : transportf_disp_mor2 p q τ
      =
      (_ ◃ idto2mor (!q)) • τ • (idto2mor p ▹ _).
  Proof.
    induction p, q.
    cbn.
    rewrite lwhisker_id2.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition two_cat_arrow_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms two_cat_arrow_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn in *.
      rewrite transportb_disp_mor2_two_cat_arrow.
      unfold two_cat_lassociator, two_cat_runitor, two_cat_linvunitor, two_cat_rassociator.
      rewrite idto2mor_lwhisker.
      rewrite idto2mor_rwhisker.
      rewrite !idto2mor_comp.
      rewrite idto2mor_rwhisker.
      rewrite !idto2mor_comp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (id1_lwhisker fg).
      }
      unfold two_cat_lunitor, two_cat_linvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      use arr_idto2mor_eq.
      apply idpath.
    - intro ; intros ; cbn in *.
      rewrite transportb_disp_mor2_two_cat_arrow.
      unfold two_cat_lassociator, two_cat_runitor, two_cat_linvunitor, two_cat_rassociator.
      rewrite idto2mor_lwhisker.
      rewrite idto2mor_rwhisker.
      rewrite !idto2mor_comp.
      rewrite idto2mor_lwhisker.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (rwhisker_id1 fg).
      }
      unfold two_cat_runitor, two_cat_rinvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      use arr_idto2mor_eq.
      apply idpath.
    - intro ; intros ; cbn in *.
      rewrite transportb_disp_mor2_two_cat_arrow.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !vassocr.
      rewrite !idto2mor_comp.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply rwhisker_comp_mor.
      }
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply rwhisker_lwhisker_mor.
        }
        unfold two_cat_lassociator, two_cat_rassociator.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply lwhisker_lwhisker_mor.
        }
        unfold two_cat_lassociator, two_cat_rassociator.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        rewrite !vassocl.
        rewrite idto2mor_comp.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        apply idpath.
      }
      rewrite !vassocr.
      refine (arr_idto2mor_eq3 _ _ _ _ _ _ _ _ _ _ _) ; apply idpath.
    - intro ; intros.
      apply isaset_two_cat_cells.
  Qed.

  Definition two_cat_arrow_twosided_disp_cat
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact two_cat_arrow_twosided_disp_cat_data.
    - exact two_cat_arrow_twosided_disp_cat_axioms.
  Defined.

  (** * 2. Univalence and strictness *)
  Proposition is_strict_two_cat_arrow_twosided_disp_cat
    : is_strict_twosided_disp_cat two_cat_arrow_twosided_disp_cat.
  Proof.
    intros x y.
    apply homset_property.
  Qed.

  Section IsoToDisp.
    Context {x y : C}
            {f g : two_cat_arrow_twosided_disp_cat x y}
            (τ : z_iso (C := hom_cat x y) f g).

    Let θ : f -->[ identity x ][ identity y ] g
      := two_cat_runitor _ • pr1 τ • two_cat_linvunitor _.

    Let θi : g -->[ identity x ][ identity y ] f
      := two_cat_runitor _ • inv_from_z_iso τ • two_cat_linvunitor _.

    Proposition z_iso_to_iso_two_cat_arrow_left
      : θ ;;2 θi = transportb_disp_mor2 (id_left _) (id_left _) (id_two_disp f).
    Proof.
      unfold θ, θi.
      rewrite transportb_disp_mor2_two_cat_arrow ; cbn.
      unfold two_cat_lassociator, two_cat_rassociator, two_cat_runitor, two_cat_linvunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      rewrite !idto2mor_comp.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply id1_lwhisker.
        }
        unfold two_cat_linvunitor, two_cat_lunitor.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply rwhisker_id1.
        }
        unfold two_cat_runitor, two_cat_rinvunitor.
        rewrite !vassocl.
        rewrite idto2mor_comp.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        apply idpath.
      }
      rewrite idto2mor_id.
      rewrite id2_right.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply (z_iso_inv_after_z_iso τ).
        }
        apply id2_left.
      }
      rewrite idto2mor_comp.
      apply maponpaths.
      apply (homset_property C).
    Qed.

    Proposition z_iso_to_iso_two_cat_arrow_right
      : θi ;;2 θ = transportb_disp_mor2 (id_left _) (id_left _) (id_two_disp g).
    Proof.
      unfold θ, θi.
      rewrite transportb_disp_mor2_two_cat_arrow ; cbn.
      unfold two_cat_lassociator, two_cat_rassociator, two_cat_runitor, two_cat_linvunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      rewrite !idto2mor_comp.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply id1_lwhisker.
        }
        unfold two_cat_linvunitor, two_cat_lunitor.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply rwhisker_id1.
        }
        unfold two_cat_runitor, two_cat_rinvunitor.
        rewrite !vassocl.
        rewrite idto2mor_comp.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        apply idpath.
      }
      rewrite idto2mor_id.
      rewrite id2_right.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply (z_iso_after_z_iso_inv τ).
        }
        apply id2_left.
      }
      rewrite idto2mor_comp.
      apply maponpaths.
      apply (homset_property C).
    Qed.

    Definition z_iso_to_iso_two_cat_arrow
      : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) f g.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact θ.
      - exact θi.
      - exact z_iso_to_iso_two_cat_arrow_left.
      - exact z_iso_to_iso_two_cat_arrow_right.
    Defined.
  End IsoToDisp.

  Section DispToIso.
    Context {x y : C}
            {f g : two_cat_arrow_twosided_disp_cat x y}
            (τ : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) f g).

    Let θ : f ==> g
      := two_cat_rinvunitor _ • pr1 τ • two_cat_lunitor _.

    Let θi : g ==> f
      := two_cat_rinvunitor _ • iso_inv_twosided_disp τ • two_cat_lunitor _.

    Proposition iso_two_cat_arrow_to_z_iso_inverses
      : is_inverse_in_precat (C := hom_cat x y) θ θi.
    Proof.
      split.
      - unfold θ, θi ; cbn.
        unfold two_cat_rinvunitor, two_cat_lunitor.
        pose (inv_after_iso_twosided_disp τ) as p.
        cbn in p.
        rewrite transportb_disp_mor2_two_cat_arrow in p.
        unfold two_cat_runitor, two_cat_linvunitor in p.
        rewrite idto2mor_lwhisker in p.
        rewrite idto2mor_rwhisker in p.
        rewrite !idto2mor_comp in p.
        assert (f = f · (identity y · identity y)) as q₁.
        {
          rewrite !id_right.
          apply idpath.
        }
        assert (identity x · identity x · f = f) as q₂.
        {
          rewrite !id_left.
          apply idpath.
        }
        simple refine (_ @ maponpaths (λ z, idto2mor q₁ • z • idto2mor q₂) p @ _) ; clear p.
        + unfold two_cat_lassociator, two_cat_rassociator.
          etrans.
          {
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            apply idpath.
          }
          refine (!_).
          rewrite !vassocr.
          rewrite idto2mor_comp.
          rewrite !vassocl.
          rewrite idto2mor_comp.
          etrans.
          {
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply rwhisker_id1.
            }
            unfold two_cat_runitor, two_cat_rinvunitor.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply id1_lwhisker.
            }
            unfold two_cat_lunitor, two_cat_linvunitor.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            rewrite idto2mor_comp.
            apply idpath.
          }
          rewrite !vassocr.
          use arr_idto2mor_eq2 ; apply idpath.
        + rewrite !idto2mor_comp.
          rewrite idto2mor_id.
          apply idpath.
      - unfold θ, θi ; cbn.
        unfold two_cat_rinvunitor, two_cat_lunitor.
        pose (iso_after_inv_twosided_disp τ) as p.
        cbn in p.
        rewrite transportb_disp_mor2_two_cat_arrow in p.
        unfold two_cat_runitor, two_cat_linvunitor in p.
        rewrite idto2mor_lwhisker in p.
        rewrite idto2mor_rwhisker in p.
        rewrite !idto2mor_comp in p.
        assert (g = g · (identity y · identity y)) as q₁.
        {
          rewrite !id_right.
          apply idpath.
        }
        assert (identity x · identity x · g = g) as q₂.
        {
          rewrite !id_left.
          apply idpath.
        }
        simple refine (_ @ maponpaths (λ z, idto2mor q₁ • z • idto2mor q₂) p @ _) ; clear p.
        + unfold two_cat_lassociator, two_cat_rassociator.
          etrans.
          {
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            apply idpath.
          }
          refine (!_).
          rewrite !vassocr.
          rewrite idto2mor_comp.
          rewrite !vassocl.
          rewrite idto2mor_comp.
          etrans.
          {
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply rwhisker_id1.
            }
            unfold two_cat_runitor, two_cat_rinvunitor.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply id1_lwhisker.
            }
            unfold two_cat_lunitor, two_cat_linvunitor.
            rewrite !vassocr.
            rewrite idto2mor_comp.
            rewrite !vassocl.
            rewrite idto2mor_comp.
            apply idpath.
          }
          rewrite !vassocr.
          use arr_idto2mor_eq2 ; apply idpath.
        + rewrite !idto2mor_comp.
          rewrite idto2mor_id.
          apply idpath.
    Qed.

    Definition iso_two_cat_arrow_to_z_iso
      : z_iso (C := hom_cat x y) f g.
    Proof.
      use make_z_iso.
      - exact θ.
      - exact θi.
      - exact iso_two_cat_arrow_to_z_iso_inverses.
    Defined.
  End DispToIso.

  Proposition iso_twosided_disp_two_cat_arrow_weq_left
              {x y : C}
              (f g : two_cat_arrow_twosided_disp_cat x y)
              (τ : z_iso (C := hom_cat x y) f g)
    : iso_two_cat_arrow_to_z_iso (z_iso_to_iso_two_cat_arrow τ) = τ.
  Proof.
    use z_iso_eq.
    cbn.
    rewrite !vassocr.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply two_cat_rinvunitor_runitor.
    }
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      apply two_cat_linvunitor_lunitor.
    }
    apply id2_right.
  Qed.

  Proposition iso_twosided_disp_two_cat_arrow_weq_right
              {x y : C}
              (f g : two_cat_arrow_twosided_disp_cat x y)
              (τ : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) f g)
    : z_iso_to_iso_two_cat_arrow (iso_two_cat_arrow_to_z_iso τ) = τ.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    cbn.
    rewrite !vassocr.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply two_cat_runitor_rinvunitor.
    }
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      apply two_cat_lunitor_linvunitor.
    }
    apply id2_right.
  Qed.

  Definition iso_twosided_disp_two_cat_arrow_weq
             {x y : C}
             (f g : two_cat_arrow_twosided_disp_cat x y)
    : z_iso (C := hom_cat x y) f g
      ≃
      iso_twosided_disp (identity_z_iso x) (identity_z_iso y) f g.
  Proof.
    use weq_iso.
    - exact z_iso_to_iso_two_cat_arrow.
    - exact iso_two_cat_arrow_to_z_iso.
    - apply iso_twosided_disp_two_cat_arrow_weq_left.
    - apply iso_twosided_disp_two_cat_arrow_weq_right.
  Defined.

  Definition is_univalent_two_cat_arrow
             (H : locally_univalent_two_cat C)
    : is_univalent_twosided_disp_cat two_cat_arrow_twosided_disp_cat.
  Proof.
    intros x x' y y' p q f g.
    induction p, q.
    use weqhomot.
    - exact (iso_twosided_disp_two_cat_arrow_weq f g ∘ make_weq _ (H x y f g))%weq.
    - intro p.
      cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      cbn.
      rewrite id2_right.
      apply idpath.
  Qed.
End TwoCatArrowTwoSidedDispCat.
