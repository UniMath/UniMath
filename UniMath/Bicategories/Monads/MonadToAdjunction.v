(*********************************************************************************

 Every monad gives rise to an adjunction

 If a bicategory has Eilenberg-Moore objects, then every monad arises from an
 adjunction. This is the so-called free-algebra adjunction with

 This generalizes the construction in Monads.MonadAlgebras.v.
 Note: since we can instantiate this construction for Kleisli objects as well, the
 construction also generalizes the construction in Monads.KleisliCategory.v

 Contents
 1. Adjunction from monad
 2. Equivalence

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.AdjunctionToMonad.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

Section MonadToAdjunction.
  Context {B : bicat}
          (HB : bicat_has_em B)
          (m : mnd B).

  Let x : B := ob_of_mnd m.
  Let f : x --> x := endo_of_mnd m.
  Let η : id₁ _ ==> f := unit_of_mnd m.
  Let μ : f · f ==> f := mult_of_mnd m.

  Let e : em_cone m := pr1 (HB m).
  Let He : has_em_ump _ e := pr2 (HB m).

  Let l : e --> x := mor_of_mnd_mor (mor_of_em_cone _ e).
  Let lf : l · f ==> l := mnd_mor_endo (mor_of_em_cone _ e) • lunitor _.

  (**
   1. Adjunction from monad
   *)
  Definition free_alg_1cell_cone
    : em_cone m.
  Proof.
    use make_em_cone.
    - exact x.
    - exact f.
    - exact (μ • linvunitor _).
    - abstract
        (refine (!(id2_left _) @ _) ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         refine (!_) ;
         exact (mnd_unit_right m)).
    - abstract
        (rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite !vassocl ;
         use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
         rewrite !vassocr ;
         rewrite rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite linvunitor_lunitor ;
         rewrite id2_right ;
         rewrite !vassocr ;
         exact (!(mnd_mult_assoc m))).
  Defined.

  Definition free_alg_1cell
    : x --> e
    := em_ump_1_mor _ He free_alg_1cell_cone.

  Definition mnd_to_unit
    : id₁ x ==> free_alg_1cell · l
    := η • cell_of_mnd_cell ((em_ump_1_inv2cell _ He free_alg_1cell_cone)^-1).

  Definition mnd_to_counit_cell_data
    : mnd_cell_data
        (# (mnd_incl B) (l · free_alg_1cell) · mor_of_em_cone m e)
        (# (mnd_incl B) (id₁ e) · mor_of_em_cone m e)
    := rassociator _ _ _
       • (_ ◃ cell_of_mnd_cell (em_ump_1_inv2cell _ He free_alg_1cell_cone))
       • mnd_mor_endo (mor_of_em_cone m e).

  Local Definition em_ump_mnd_cell_endo_help
    : (_ ◃ mnd_mor_endo (mor_of_em_cone m e))
      • lassociator _ _ _
      • (runitor _ ▹ _)
      • cell_of_mnd_cell (em_ump_1_inv2cell m He free_alg_1cell_cone)
      =
      lassociator _ _ _
      • (cell_of_mnd_cell (em_ump_1_inv2cell m He free_alg_1cell_cone) ▹ endo_of_mnd m)
      • μ.
  Proof.
    refine (_ @ vassocr _ _ _).
    use vcomp_move_L_pM ; [ is_iso | ].
    use (vcomp_rcancel (linvunitor _)) ; [ is_iso | ].
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite linvunitor_assoc.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      apply idpath.
    }
    refine (_ @ mnd_cell_endo (em_ump_1_inv2cell m He free_alg_1cell_cone)).
    rewrite !vassocr.
    apply idpath.
  Qed.

  Definition mnd_to_counit_is_mnd_cell
    : is_mnd_cell mnd_to_counit_cell_data.
  Proof.
    unfold is_mnd_cell ; cbn.
    unfold mnd_to_counit_cell_data.
    rewrite runitor_lunitor_identity.
    rewrite lunitor_linvunitor.
    rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite !vassocl.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    rewrite !vassocr.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    etrans.
    {
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite <- inverse_pentagon_3.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        rewrite rwhisker_vcomp.
        apply maponpaths.
        rewrite linvunitor_assoc.
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        rewrite id2_right.
        rewrite <- runitor_triangle.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          rewrite vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        rewrite rwhisker_hcomp.
        rewrite !vassocl.
        rewrite <- inverse_pentagon_4.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite !vassocr.
      apply em_ump_mnd_cell_endo_help.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    rewrite <- rassociator_rassociator.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      apply idpath.
    }
    use vcomp_move_R_pM ; [ is_iso | ].
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ].
    refine (!_).
    refine (_ @ mnd_mor_mu (mor_of_em_cone m e)).
    rewrite !vassocl.
    do 4 apply maponpaths.
    refine (!_).
    apply lunitor_triangle.
  Qed.

  Definition mnd_to_counit_mnd_cell
    : # (mnd_incl B) (l · free_alg_1cell) · mor_of_em_cone m e
      ==>
      # (mnd_incl B) (id₁ e) · mor_of_em_cone m e.
  Proof.
    use make_mnd_cell.
    - exact mnd_to_counit_cell_data.
    - exact mnd_to_counit_is_mnd_cell.
  Defined.

  Definition mnd_to_counit
    : l · free_alg_1cell ==> id₁ e
    := em_ump_2_cell _ He mnd_to_counit_mnd_cell.

  Definition mnd_to_left_adjoint_data
    : left_adjoint_data free_alg_1cell
    := l ,, (mnd_to_unit ,, mnd_to_counit).

  Local Definition em_ump_mnd_cell_endo_inv_help
    : (cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1) ▹ endo_of_mnd m)
      • rassociator _ _ _
      • (_ ◃ mnd_mor_endo (mor_of_em_cone m e))
      =
      μ
      • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1)
      • (_ ◃ linvunitor _).
  Proof.
    use (vcomp_rcancel (lassociator _ _ _ • ((runitor _) ▹ _) • linvunitor _)) ; [ is_iso | ].
    refine (!_).
    etrans.
    {
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite lwhisker_hcomp.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply triangle_l_inv.
      }
      rewrite <- rwhisker_hcomp.
      apply maponpaths_2.
      refine (rwhisker_vcomp _ _ _ @ _).
      rewrite rinvunitor_runitor.
      apply id2_rwhisker.
    }
    rewrite id2_left.
    rewrite linvunitor_natural.
    rewrite <- lwhisker_hcomp.
    refine (vassocr _ _ _ @ _).
    refine (mnd_cell_endo ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1) @ _).
    rewrite !vassocl.
    apply maponpaths.
    cbn.
    rewrite !vassocl.
    do 3 apply maponpaths.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite linvunitor_assoc.
    apply idpath.
  Qed.

  Definition mnd_to_left_adjoint_axioms
    : left_adjoint_axioms mnd_to_left_adjoint_data.
  Proof.
    split.
    - use (em_ump_eq _ He).
      + apply id₂.
      + use eq_mnd_cell ; cbn.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !rwhisker_hcomp.
          rewrite <- triangle_l.
          rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          apply maponpaths_2.
          do 2 apply maponpaths.
          exact (maponpaths
                   cell_of_mnd_cell
                   (em_ump_2_eq _ He mnd_to_counit_mnd_cell)).
        }
        cbn ; unfold mnd_to_counit_cell_data.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite <- !lwhisker_vcomp.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        unfold mnd_to_unit.
        rewrite !vassocr.
        rewrite <- linvunitor_assoc.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          apply em_ump_mnd_cell_endo_inv_help.
        }
        etrans.
        {
          rewrite !vassocr.
          etrans.
          {
            do 5 apply maponpaths_2.
            rewrite lwhisker_hcomp.
            rewrite <- linvunitor_natural.
            apply idpath.
          }
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            do 3 apply maponpaths_2.
            apply mnd_unit_left.
          }
          rewrite id2_left.
          rewrite !vassocr.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            exact (maponpaths
                     cell_of_mnd_cell
                     (vcomp_rinv (em_ump_1_inv2cell m He free_alg_1cell_cone))).
          }
          apply id2_left.
        }
        rewrite lwhisker_vcomp.
        rewrite linvunitor_lunitor.
        apply lwhisker_id2.
      + rewrite psfunctor_id2.
        apply id2_rwhisker.
    - cbn.
      rewrite !vassocl.
      unfold mnd_to_unit.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        apply maponpaths_2.
        exact (maponpaths
                 cell_of_mnd_cell
                 (em_ump_2_eq _ He mnd_to_counit_mnd_cell)).
      }
      simpl.
      unfold mnd_to_counit_cell_data.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        do 2 apply maponpaths_2.
        apply maponpaths.
        exact (maponpaths
                 cell_of_mnd_cell
                 (vcomp_linv (em_ump_1_inv2cell m He free_alg_1cell_cone))).
      }
      cbn.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ].
      refine (!(mnd_mor_unit (mor_of_em_cone m e)) @ _).
      cbn.
      rewrite id2_rwhisker.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition mnd_to_left_adjoint
    : left_adjoint free_alg_1cell
    := mnd_to_left_adjoint_data ,, mnd_to_left_adjoint_axioms.

  Definition mnd_to_adjunction
    : adjunction x e
    := free_alg_1cell ,, mnd_to_left_adjoint.

  (**
   2. Equivalence
   *)
  Definition mnd_to_adjunction_to_mnd_data
    : mnd_mor_data
        (mnd_from_adjunction mnd_to_adjunction)
        m.
  Proof.
    use make_mnd_mor_data.
    - exact (id₁ _).
    - exact (lunitor _
             • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone)^-1)
             • rinvunitor _).
  Defined.

  Definition mnd_to_adjunction_to_mnd_law₁
    : linvunitor (id₁ x)
      • (mnd_to_unit ▹ id₁ x)
      =
      rinvunitor (id₁ x)
      • (id₁ x ◃ unit_of_mnd m)
      • ((lunitor f • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1))
     • rinvunitor _).
  Proof.
    rewrite lunitor_V_id_is_left_unit_V_id.
    rewrite !vassocl.
    apply maponpaths.
    unfold mnd_to_unit.
    rewrite !vassocr.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lunitor_runitor_identity.
    rewrite runitor_rinvunitor.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition mnd_to_adjunction_to_mnd_law₂
    : lassociator (id₁ _) f f
      • ((lunitor f
          • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1)
          • rinvunitor (em_ump_1_mor m He free_alg_1cell_cone · pr1 (mor_of_em_cone m e)))
         ▹ endo_of_mnd m)
      • rassociator (free_alg_1cell · l) (id₁ x) f
      • (free_alg_1cell · l
           ◃ (lunitor f
              • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1)
              • rinvunitor (em_ump_1_mor m He free_alg_1cell_cone · pr1 (mor_of_em_cone m e))))
      • lassociator (free_alg_1cell · l) (free_alg_1cell · l) (id₁ x)
      • ((((rassociator free_alg_1cell l (free_alg_1cell · l)
            • (free_alg_1cell ◃ lassociator l free_alg_1cell l))
            • (free_alg_1cell ◃ (mnd_to_counit ▹ l)))
            • (free_alg_1cell ◃ lunitor l)) ▹ id₁ x)
      =
      (id₁ x ◃ μ)
      • ((lunitor f • cell_of_mnd_cell ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1))
      • rinvunitor (em_ump_1_mor m He free_alg_1cell_cone · pr1 (mor_of_em_cone m e))).
  Proof.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 7 apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
    }
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite !vassocl.
      rewrite !rwhisker_vcomp.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 4 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      pose (p := maponpaths cell_of_mnd_cell (em_ump_2_eq m He mnd_to_counit_mnd_cell)).
      cbn in p.
      exact p.
    }
    unfold mnd_to_counit_cell_data.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocr.
        apply maponpaths_2.
        apply lwhisker_lwhisker_rassociator.
      }
      apply maponpaths_2.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite lwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 cell_of_mnd_cell
                 (vcomp_linv (em_ump_1_inv2cell m He free_alg_1cell_cone))).
      }
      apply lwhisker_id2.
    }
    rewrite id2_left.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    use (vcomp_rcancel (linvunitor _)) ; [ is_iso | ].
    pose (p := mnd_cell_endo ((em_ump_1_inv2cell m He free_alg_1cell_cone) ^-1)).
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocr.
      exact p.
    }
    apply maponpaths.
    cbn.
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    rewrite <- linvunitor_assoc.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- !lwhisker_vcomp.
    rewrite runitor_rwhisker.
    apply idpath.
  Qed.

  Definition mnd_to_adjunction_to_mnd_laws
    : mnd_mor_laws mnd_to_adjunction_to_mnd_data.
  Proof.
    split.
    - exact mnd_to_adjunction_to_mnd_law₁.
    - exact mnd_to_adjunction_to_mnd_law₂.
  Qed.

  Definition mnd_to_adjunction_to_mnd
    : mnd_from_adjunction mnd_to_adjunction
      -->
      m.
  Proof.
    use make_mnd_mor.
    - exact mnd_to_adjunction_to_mnd_data.
    - exact mnd_to_adjunction_to_mnd_laws.
  Defined.

  Definition mnd_to_adjunction_to_mnd_adj_equivalence
             (HB_2_0 : is_univalent_2_0 B)
    : left_adjoint_equivalence mnd_to_adjunction_to_mnd.
  Proof.
    use to_equivalence_mnd.
    - exact HB_2_0.
    - apply internal_adjoint_equivalence_identity.
    - cbn.
      is_iso.
      apply (from_invertible_mnd_2cell
               (inv_of_invertible_2cell (em_ump_1_inv2cell m He free_alg_1cell_cone))).
  Defined.
End MonadToAdjunction.
