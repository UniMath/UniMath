Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.LaxTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Composition.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Sigma.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.

Section MonadBicategory.
  Variable (C : bicat).

  Definition plain_monad
    : bicat
    := bicat_algebra (ps_id_functor C).

  Definition plain_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 plain_monad.
  Proof.
    apply bicat_algebra_is_univalent_2_1.
    exact HC_1.
  Defined.

  Definition plain_monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 plain_monad.
  Proof.
    apply bicat_algebra_is_univalent_2_0.
    - exact HC_0.
    - exact HC_1.
  Defined.

  Definition unit_left_data
    : laxtrans_data
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use mk_laxtrans_data.
    - exact (λ X, id₁ (pr1 X)).
    - exact (λ X Y f, lunitor (pr1 f) • rinvunitor (pr1 f)).
  Defined.

  Definition unit_left_is_laxtrans
    : is_laxtrans unit_left_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros X ; cbn in *.
      rewrite !vassocr.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_linvunitor, id2_left.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite !vassocr.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor, id2_left.
      rewrite rwhisker_hcomp.
      rewrite id2_right.
      reflexivity.
    - intros X Y Z f g ; cbn in *.
      rewrite !id2_left.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_hcomp.
      rewrite triangle_l.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite !id2_left, id2_rwhisker, id2_right.
      rewrite rinvunitor_triangle.
      reflexivity.
  Qed.

  Definition unit_left
    : pstrans
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use mk_pstrans.
    - use mk_laxtrans.
      + exact unit_left_data.
      + exact unit_left_is_laxtrans.
    - intros X Y f ; cbn.
      is_iso.
  Defined.

  Definition unit_right_data
    : laxtrans_data
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use mk_laxtrans_data.
    - exact (λ X, pr2 X).
    - exact (λ X Y f, pr2 f).
  Defined.

  Definition unit_right_laws
    : is_laxtrans unit_right_data.
  Proof.
    repeat split.
    - exact (λ X Y f g α, !(pr2 α)).
    - intros X ; cbn in *.
      rewrite lwhisker_id2, id2_left, !id2_right.
      reflexivity.
    - intros ; cbn in *.
      rewrite !lwhisker_id2, !id2_rwhisker, !id2_left, !id2_right.
      rewrite !id2_rwhisker, !id2_right.
      reflexivity.
  Qed.

  Definition unit_right
    : laxtrans
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use tpair.
    - exact unit_right_data.
    - exact unit_right_laws.
  Defined.

  Definition add_unit
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact unit_left.
    - exact unit_right.
  Defined.

  Definition bind_right_data
    : laxtrans_data
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use mk_laxtrans_data.
    - exact (λ X, pr2 X · pr2 X).
    - exact (λ X Y f,
             (rassociator (pr2 X) (pr2 X) (pr1 f))
               • (pr2 X ◃ pr2 f)
               • lassociator (pr2 X) (pr1 f) (pr2 Y)
               • (pr2 f ▹ pr2 Y)
               • rassociator (pr1 f) (pr2 Y) (pr2 Y)).
  Defined.

  Definition bind_right_laws
    : is_laxtrans bind_right_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn in *.
      unfold total_prebicat_cell_struct in * ; cbn in *.
      unfold alg_disp_cat_2cell in * ; cbn in *.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      refine (_ @ !(maponpaths (λ z, ((_ ◃ z) • _) • _) (pr2 α))).
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      repeat (apply maponpaths).
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      exact (!(pr2 α)).
    - intros X ; cbn in *.
      rewrite !lwhisker_id2, !id2_rwhisker, !id2_left, !id2_right.
      rewrite id2_rwhisker, id2_right.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_triangle.
      rewrite !vassocl.
      repeat apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite linvunitor_assoc.
      reflexivity.
    - intros ; cbn in *.
      rewrite !lwhisker_id2, !id2_rwhisker, !id2_left, !id2_right.
      rewrite !id2_rwhisker, !id2_right.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      rewrite pentagon.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator, id2_rwhisker, id2_left.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      pose (pentagon (pr2 Z) (pr1 g) (pr1 f) (pr2 X)) as pent.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp, !vassocr in pent.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite <- pent ; clear pent.
      rewrite !vassocl.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      pose (pentagon (pr1 g) (pr2 Y) (pr1 f) (pr2 X)) as pent.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp, !vassocr in pent.
      refine (!(_ @ _)).
      {
        do 9 apply maponpaths_2.
        exact (!pent).
      }
      clear pent.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      pose (inverse_pentagon (pr1 g) (pr2 Y) (pr2 Y) (pr1 f)) as pent.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp, !vassocr in pent.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      etrans.
      {
        do 3 apply maponpaths.
        do 5 apply maponpaths_2.
        exact (!pent).
      }
      clear pent.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lassociator_rassociator, id2_left.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      rewrite inverse_pentagon.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • (_ • z))))) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator, id2_rwhisker, id2_left.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_R_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      pose (inverse_pentagon (pr2 Z) (pr1 g) (pr2 Y) (pr1 f)) as pent.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in pent.
      refine (!(_ @ _)).
      {
        do 3 apply maponpaths.
        exact (!pent).
      }
      clear pent.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lassociator_rassociator, id2_left.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      reflexivity.
  Qed.

  Definition bind_right
    : laxtrans
        (@ps_comp _ (total_bicat (disp_alg_bicat (ps_id_functor C))) _
                  (pr1_psfunctor (disp_alg_bicat (ps_id_functor C)))
                  (ps_id_functor (total_bicat (disp_alg_bicat (ps_id_functor C)))))
        (pr1_psfunctor (disp_alg_bicat (ps_id_functor C))).
  Proof.
    use tpair.
    - exact bind_right_data.
    - exact bind_right_laws.
  Defined.

  Definition add_bind
    : disp_bicat plain_monad.
  Proof.
    use add_cell_disp_cat.
    - exact (ps_id_functor _).
    - exact bind_right.
    - exact unit_right.
  Defined.

  Definition add_unit_bind
    : disp_bicat plain_monad
    := disp_dirprod_bicat add_unit add_bind.

  Definition lawless_monad := total_bicat add_unit_bind.

  Definition lawless_monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 lawless_monad.
  Proof.
    apply total_is_locally_univalent.
    - exact (plain_monad_is_univalent_2_1 HC_1).
    - apply is_univalent_2_1_dirprod_bicat.
      * apply add_cell_disp_cat_locally_univalent.
      * apply add_cell_disp_cat_locally_univalent.
  Defined.

  Definition lawless_monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 lawless_monad.
  Proof.
    apply total_is_univalent_2_0.
    - exact (plain_monad_is_univalent_2_0 HC_0 HC_1).
    - apply is_univalent_2_0_dirprod_bicat.
      + exact (plain_monad_is_univalent_2_1 HC_1).
      + apply add_cell_disp_cat_univalent_2_0.
        * exact HC_1.
        * apply disp_alg_bicat_locally_univalent.
      + apply add_cell_disp_cat_univalent_2_0.
        * exact HC_1.
        * apply disp_alg_bicat_locally_univalent.
      + apply add_cell_disp_cat_locally_univalent.
      + apply add_cell_disp_cat_locally_univalent.
  Defined.

  Definition monad_obj : lawless_monad → C
    := λ m, pr1 (pr1 m).

  Definition monad_map : ∏ (m : lawless_monad), monad_obj m --> monad_obj m
    := λ m, pr2(pr1 m).

  Definition monad_unit : ∏ (m : lawless_monad), id₁ (monad_obj m) ==> monad_map m
    := λ m, pr1(pr2 m).

  Definition monad_bind
    : ∏ (m : lawless_monad), monad_map m · monad_map m ==> monad_map m
    := λ m, pr2(pr2 m).

  Definition monad_laws (m : lawless_monad) : UU
    := ((linvunitor (monad_map m))
          • (monad_unit m ▹ monad_map m)
          • monad_bind m
        =
        id₂ (monad_map m))
       ×
       ((rinvunitor (monad_map m))
          • (monad_map m ◃ monad_unit m)
          • monad_bind m
        =
        id₂ (monad_map m))
       ×
       ((monad_map m ◃ monad_bind m)
          • monad_bind m
        =
        (lassociator (monad_map m) (monad_map m) (monad_map m))
          • (monad_bind m ▹ monad_map m)
          • monad_bind m).

  Definition monad := fullsubbicat lawless_monad monad_laws.

  Definition mk_monad
             (X : C)
             (f : C⟦X,X⟧)
             (η : id₁ X ==> f)
             (μ : f · f ==> f)
             (ημ : linvunitor f • (η ▹ f) • μ
                   =
                   id₂ f)
             (μη : rinvunitor f • (f ◃ η) • μ
                   =
                   id₂ f)
             (μμ : (f ◃ μ) • μ
                   =
                   lassociator f f f • (μ ▹ f) • μ)
    : monad.
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact X.
        * exact f.
      + split.
        * exact η.
        * exact μ.
    - repeat split.
      + exact ημ.
      + exact μη.
      + exact μμ.
  Defined.

  Definition monad_is_univalent_2_1
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_1 monad.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply lawless_monad_is_univalent_2_1.
    exact HC_1.
  Defined.

  Definition monad_is_univalent_2_0
             (HC_0 : is_univalent_2_0 C)
             (HC_1 : is_univalent_2_1 C)
    : is_univalent_2_0 monad.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - exact (lawless_monad_is_univalent_2_0 HC_0 HC_1).
    - exact (lawless_monad_is_univalent_2_1 HC_1).
    - intro ; simpl.
      repeat (apply isapropdirprod) ; apply C.
  Defined.
End MonadBicategory.