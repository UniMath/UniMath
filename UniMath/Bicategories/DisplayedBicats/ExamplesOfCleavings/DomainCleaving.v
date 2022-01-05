Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Domain.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

(**
The domain displayed bicategory has a cleaving
 *)
Section DomainCleaving.
  Context {B : bicat}
          (a : B).

  (** Every 2-cell is cartesian *)
  Definition dom_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : dom_disp_bicat B a c₁}
             {t₂ : dom_disp_bicat B a c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
    : is_cartesian_2cell (dom_disp_bicat B a) αα.
  Proof.
    intros s₃ ss₃ γ γα.
    use iscontraprop1.
    - use isaproptotal2.
      + intro ; apply (dom_disp_bicat B a).
      + intros.
        apply cellset_property.
    - simple refine (_ ,, _).
      + cbn in *.
        rewrite γα, αα.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_vcomp.
        apply idpath.
      + apply cellset_property.
  Qed.

  Definition dom_local_cleaving
    : local_cleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _) ; cbn.
    - exact ((β ▹ t₂) • α).
    - simple refine (idpath _ ,, _).
      apply dom_is_cartesian_2cell.
  Defined.

  (** Characterizations of cartesian 1-cells *)
  Definition dom_invertible_2cell_is_cartesian_1cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : dom_disp_bicat B a c₁}
             {t₂ : dom_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : is_invertible_2cell ss)
    : cartesian_1cell (dom_disp_bicat B a) ss.
  Proof.
    split.
    - intros c₃ t₃ s' ss'.
      simple refine (_ ,, _).
      + exact ((s' ◃ Hss^-1) • lassociator _ _ _ • ss').
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite id2_rwhisker ;
             etrans ;
             [ apply maponpaths_2 ;
               rewrite !vassocl ;
               rewrite lwhisker_vcomp ;
               rewrite vcomp_rinv ;
               rewrite lwhisker_id2 ;
               apply id2_right
             | ] ;
             apply rassociator_lassociator).
        * apply dom_disp_locally_groupoid.
    - cbn.
      intros c₃ t₃ s₁ s₂ α αα β ββ Lh Lh' ; cbn in *.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply (dom_disp_bicat B a) | ] ;
           apply cellset_property).
      + cbn.
        simple  refine (_ ,, _).
        * abstract
            (use (vcomp_lcancel (s₁ ◃ ss)) ; [ is_iso ; apply Hss | ] ;
             use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ] ;
             rewrite !vassocr ;
             refine (pr12 Lh @ _) ;
             cbn ;
             rewrite id2_rwhisker, id2_left ;
             rewrite ββ ;
             pose (p := pr12 Lh') ;
             cbn in p ;
             rewrite id2_rwhisker, id2_left in p ;
              etrans ; [apply maponpaths ; exact (!p) |] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite rwhisker_rwhisker_alt ;
             rewrite !vassocl ;
             rewrite vcomp_whisker ;
             apply idpath).
        * apply cellset_property.
  Defined.

  Definition dom_cartesian_1cell_is_invertible_2cell
             {c₁ c₂ : B}
             {s : c₁ --> c₂}
             {t₁ : dom_disp_bicat B a c₁}
             {t₂ : dom_disp_bicat B a c₂}
             (ss : t₁ -->[ s ] t₂)
             (Hss : cartesian_1cell (dom_disp_bicat B a) ss)
    : is_invertible_2cell ss.
  Proof.
    cbn in *.
    pose (pr1 Hss c₁ (s · t₂) (id₁ _) (rassociator _ _ _ • lunitor _)) as p.
    unfold lift_1cell_factor in p.
    cbn in p.
    pose (maponpaths (λ z, lassociator _ _ _ • z) (pr12 p)) as d.
    cbn in d.
    rewrite id2_rwhisker in d.
    rewrite id2_left in d.
    rewrite !vassocr in d.
    rewrite !lassociator_rassociator in d.
    rewrite !id2_left in d.
    use make_is_invertible_2cell.
    - exact (linvunitor _ • pr1 p).
    - rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite d.
      rewrite linvunitor_lunitor.
      apply idpath.
    - pose (@cartesian_1cell_lift_2cell
              _ _ _ _ _ _ _ _ Hss
              c₁
              t₁
              (id₁ _) (id₁ _)
              (rassociator _ _ _ • lunitor _ • ss)
              (rassociator _ _ _ • lunitor _ • ss)
              (id2 _)) as lift2.
      cbn in lift2.
      rewrite !id2_rwhisker, !id2_left in lift2.
      pose (lift2 (idpath _)) as l'.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      refine (_ @ id2_left _).
      use (l' (pr1 p • ss ,, _) (lunitor _ ,, _)) ; cbn.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_left.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite d.
          apply idpath.
        * apply dom_disp_locally_groupoid.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_left.
          rewrite !vassocl.
          rewrite vcomp_lunitor.
          apply idpath.
        * apply dom_disp_locally_groupoid.
  Qed.

  Definition dom_global_cleaving
    : global_cleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ s.
    simple refine (s · t₁ ,, id₂ _ ,, _) ; cbn.
    apply dom_invertible_2cell_is_cartesian_1cell.
    is_iso.
  Defined.

  Definition dom_cleaving_of_bicats
    : cleaving_of_bicats (dom_disp_bicat B a).
  Proof.
    repeat split.
    - exact dom_local_cleaving.
    - exact dom_global_cleaving.
    - intro ; intros.
      apply dom_is_cartesian_2cell.
    - intro ; intros.
      apply dom_is_cartesian_2cell.
  Defined.
End DomainCleaving.
