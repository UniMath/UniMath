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
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Domain.

Local Open Scope cat.

(**
The domain displayed bicategory has a cleaving
 *)
Section DomainCleaving.
  Context {B : bicat}
          (a : B).

  (** Every 2-cell is opcartesian *)
  Definition dom_is_opcartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : dom_disp_bicat B a c₁}
             {t₂ : dom_disp_bicat B a c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
    : is_opcartesian_2cell (dom_disp_bicat B a) αα.
  Proof.
    intros s₃ ss₃ γ γα.
    use iscontraprop1.
    - use isaproptotal2.
      + intro ; apply (dom_disp_bicat B a).
      + intros.
        apply cellset_property.
    - simple refine (_ ,, _).
      + cbn in *.
        rewrite <- γα, <- αα.
        rewrite !vassocl.
        apply maponpaths.
        rewrite rwhisker_vcomp.
        apply idpath.
      + apply cellset_property.
  Qed.

  Definition dom_local_cleaving
    : local_opcleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _) ; cbn.
    - exact (α • (β ▹ t₂)).
    - simple refine (idpath _ ,, _).
      apply dom_is_opcartesian_2cell.
  Defined.

  Definition dom_local_iso_cleaving
    : local_iso_cleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (α • (β^-1 ▹ s₂) ,, _ ,, _).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite rwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite id2_rwhisker ;
         apply id2_right).
    - apply dom_disp_locally_groupoid.
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
      + exact (ss' • rassociator _ _ _ • (s' ◃ Hss^-1)).
      + simple refine (_ ,, _).
        * abstract
            (cbn ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite !vassocl ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite lwhisker_id2 ;
             rewrite id2_left ;
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
            (pose (pr12 Lh') as p ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             use (vcomp_rcancel (s₂ ◃ ss)) ; [ is_iso ; apply Hss | ] ;
             use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
             refine (_ @ !p) ; clear p ;
             rewrite !vassocl ;
             pose (pr12 Lh) as p ;
             refine (_ @ ββ) ;
             cbn in p ;
             rewrite id2_rwhisker in p ;
             rewrite id2_right in p ;
             refine (_ @ maponpaths (λ z, z • _) p) ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             rewrite vcomp_whisker ;
             rewrite !vassocl ;
             rewrite rwhisker_rwhisker ;
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
    pose (pr1 Hss c₁ (s · t₂) (id₁ _) (linvunitor _ • lassociator _ _ _)) as p.
    unfold lift_1cell_factor in p.
    cbn in p.
    pose (maponpaths (λ z, z • rassociator _ _ _) (pr12 p)) as d.
    cbn in d.
    rewrite id2_rwhisker in d.
    rewrite id2_right in d.
    rewrite !vassocl in d.
    rewrite !lassociator_rassociator in d.
    rewrite !id2_right in d.
    use make_is_invertible_2cell.
    - exact (pr1 p • lunitor _).
    - pose (@cartesian_1cell_lift_2cell
              _ _ _ _ _ _ _ _ Hss
              c₁
              t₁
              (id₁ _) (id₁ _)
              (ss • linvunitor _ • lassociator _ _ _)
              (ss • linvunitor _ • lassociator _ _ _)
              (id2 _)) as lift2.
      cbn in lift2.
      rewrite !id2_rwhisker, !id2_right in lift2.
      pose (lift2 (idpath _)) as l'.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left.
      refine (!(id2_right _) @ _).
      use (l' (ss • pr1 p ,, _) (linvunitor _ ,, _)) ; cbn.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_right.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite d.
          apply idpath.
        * apply dom_disp_locally_groupoid.
      + simple refine (_ ,, _).
        * cbn.
          rewrite id2_rwhisker, id2_right.
          apply maponpaths_2.
          rewrite linvunitor_natural.
          rewrite <- lwhisker_hcomp.
          apply idpath.
        * apply dom_disp_locally_groupoid.
    - rewrite !vassocl.
      rewrite <- vcomp_lunitor.
      rewrite !vassocr.
      rewrite d.
      apply linvunitor_lunitor.
  Qed.

  Definition dom_global_cleaving
    : global_cleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ s.
    simple refine (s · t₁ ,, id₂ _ ,, _) ; cbn.
    apply dom_invertible_2cell_is_cartesian_1cell.
    is_iso.
  Defined.
End DomainCleaving.
