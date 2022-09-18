(***********************************************************************************

 Monads can be composed if we have a distributive law between them

 This results holds for monads in arbitrary bicategories. For monads of categories,
 this was already proved in Monads.Derivative.v (`monad_comp`)

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.DistributiveLaws.

Local Open Scope cat.

Section ComposeMonad.
  Context {B : bicat}
          {x : B}
          (dm₁ dm₂ : disp_mnd B x)
          (α : distr_law dm₁ dm₂).

  Let m₁ : mnd B := x ,, dm₁.
  Let m₂ : mnd B := x ,, dm₂.

  Let f : x --> x := endo_of_mnd m₁.
  Let g : x --> x := endo_of_mnd m₂.

  Let η₁ : id₁ _ ==> f := unit_of_mnd m₁.
  Let η₂ : id₁ _ ==> g := unit_of_mnd m₂.

  Let μ₁ : f · f ==> f := mult_of_mnd m₁.
  Let μ₂ : g · g ==> g := mult_of_mnd m₂.

  Let ηc : id₁ x ==> f · g
    := linvunitor _ • (η₁ ▹ _) • (_ ◃ η₂).

  Let μc
    : f · g · (f · g) ==> f · g
    := rassociator _ _ _
       • (f ◃ lassociator _ _ _)
       • (f ◃ (α ▹ g))
       • (f ◃ rassociator _ _ _)
       • lassociator _ _ _
       • (μ₁ ▹ _)
       • (_ ◃ μ₂).

  Definition compose_mnd_unit_left
    : (linvunitor (f · g) • (ηc ▹ f · g)) • μc = id₂ (f · g).
  Proof.
    unfold ηc, μc.
    clear ηc μc.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      rewrite !vassocr.
      apply maponpaths.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite <- rinvunitor_natural.
      apply idpath.
    }
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite <- rassociator_rassociator.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
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
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite !rwhisker_vcomp.
      do 5 apply maponpaths_2.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- inverse_pentagon_2.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        do 2 apply maponpaths_2.
        apply maponpaths.
        exact (!(unit_law_2_from_distr_law α)).
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      do 2 apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      exact (pr12 dm₁).
    }
    rewrite id2_left.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      apply idpath.
    }
    rewrite vassocr.
    rewrite rwhisker_hcomp.
    rewrite !vassocr.
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !lwhisker_vcomp.
    refine (_ @ lwhisker_id2 _ _).
    apply maponpaths.
    exact (pr12 dm₂).
  Qed.

  Definition compose_mnd_unit_right
    : (rinvunitor (f · g) • (f · g ◃ ηc)) • μc = id₂ (f · g).
  Proof.
    unfold ηc, μc.
    clear ηc μc.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      rewrite !vassocr.
      apply maponpaths.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite <- rinvunitor_natural.
      apply idpath.
    }
    rewrite <- rinvunitor_triangle.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite vcomp_whisker.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      do 4 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- left_unit_inv_assoc.
      rewrite lwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply (pr122 dm₂).
      }
      apply lwhisker_id2.
    }
    rewrite id2_right.
    rewrite !vassocr.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      exact (!(unit_law_1_from_distr_law α)).
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_hcomp.
    rewrite triangle_l_inv.
    rewrite <- rwhisker_hcomp.
    rewrite rwhisker_vcomp.
    refine (_ @ id2_rwhisker _ _).
    apply maponpaths.
    rewrite vassocr.
    apply (pr122 dm₁).
  Qed.

  Definition compose_mnd_assoc
    : (rassociator (f · g) (f · g) (f · g) • (f · g ◃ μc)) • μc
      =
        (μc ▹ f · g) • μc.
  Proof.
    unfold μc.
    rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
    clear ηc μc.
    rewrite !vassocl.
    etrans.
    {
      do 7 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite lwhisker_lwhisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- vcomp_whisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      do 2 apply maponpaths.
      pose (maponpaths (λ z, lassociator _ _ _ • z) (pr222 dm₂)
             : lassociator _ _ _ • (rassociator _ _ _ • (g ◃ μ₂) • μ₂)
               =
               lassociator _ _ _ • ((μ₂ ▹ g) • μ₂)) as p.
      cbn in p.
      rewrite !vassocr in p.
      rewrite lassociator_rassociator, id2_left in p.
      exact p.
    }
    etrans.
    {
      do 12 apply maponpaths.
      rewrite vcomp_whisker.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_whisker.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
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
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      pose (pr222 dm₁
             : rassociator _ _ _ • (f ◃ μ₁) • μ₁
               =
               (μ₁ ▹ f) • μ₁) as p.
      cbn in p.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!p).
      }
      clear p.
      rewrite vcomp_whisker.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 11 apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      etrans.
      {
        do 3 apply maponpaths.
        exact (!(mu_law_2_from_distr_law α)).
      }
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 12 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 6 apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_lwhisker.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_vcomp.
      etrans.
      {
        do 3 apply maponpaths_2.
        do 2 apply maponpaths.
        exact (!(mu_law_1_from_distr_law α)).
      }
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 5 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_rwhisker_alt.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    do 4 (use vcomp_move_R_Mp ; [ is_iso | ]) ; cbn.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 11 apply maponpaths.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_4.
        rewrite <- rwhisker_hcomp.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite rwhisker_lwhisker_rassociator.
        apply maponpaths.
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite rassociator_rassociator.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rassociator_lassociator.
      rewrite id2_right.
      apply idpath.
    }
    etrans.
    {
      do 10 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_rwhisker_alt.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker_rassociator.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 5 apply maponpaths.
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite lassociator_lassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_rwhisker.
      apply idpath.
    }
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite lwhisker_lwhisker.
        rewrite <- lwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite lwhisker_lwhisker.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- vcomp_whisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      apply idpath.
    }
    do 2 (use vcomp_move_L_pM ; [ is_iso | ]) ; cbn.
    etrans.
    {
      rewrite !vassocr.
      do 5 apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rassociator_rassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_lwhisker.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        apply id2_left.
      }
      rewrite <- lwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    do 5 (use vcomp_move_L_pM ; [ is_iso | ]) ; cbn.
    etrans.
    {
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite inverse_pentagon_6.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !lwhisker_vcomp.
      do 2 apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite pentagon_6.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite <- !lwhisker_vcomp.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite !lwhisker_id2.
        apply idpath.
      }
      apply id2_right.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- lwhisker_lwhisker.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite !lwhisker_vcomp.
    rewrite lwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    refine (!_).
    rewrite rwhisker_hcomp.
    rewrite inverse_pentagon_2.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite !vassocr.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocl.
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
      apply id2_left.
    }
    rewrite lassociator_rassociator.
    rewrite id2_right.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_lassociator.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite lwhisker_lwhisker.
    apply idpath.
  Qed.

  Definition compose_mnd
    : mnd B.
  Proof.
    use make_mnd.
    - use make_mnd_data.
      + exact x.
      + exact (f · g).
      + exact ηc.
      + exact μc.
    - repeat split.
      + exact compose_mnd_unit_left.
      + exact compose_mnd_unit_right.
      + exact compose_mnd_assoc.
  Defined.
End ComposeMonad.
