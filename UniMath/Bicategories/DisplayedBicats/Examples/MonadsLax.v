(***********************************************************************

 The bicategory of monads and lax morphisms

 We define the bicategory of monads and lax morphisms.

 Note: this is a different bicategory from the one defined in Monads.v.
 The bicategory defined in that file has 1-cells that preserve the unit
 and multiplication up to invertible 2-cell. The formal theory of monads
 as described by Street, makes use of the bicategory defined in this
 file.

 Contents
 1. The bicategory
 2. The univalence
 3. Projections and constructions
 4. Invertible 2-cells
 5. Equivalences of monads
 6. Underlying pseudofunctor

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.

Local Open Scope cat.

Section Monad.
  Context (B : bicat).

  (**
   1. The bicategory
   *)
  Definition disp_add_unit_cat_ob_mor
    : disp_cat_ob_mor (end_bicat B).
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ mx, id₁ _ ==> pr2 mx).
    - exact (λ mx my ηx ηy f,
             linvunitor _ • (ηx ▹ (pr1 f))
             =
             rinvunitor _ • (pr1 f ◃ ηy) • pr2 f).
  Defined.

  Definition disp_add_unit_cat_id_comp
    : disp_cat_id_comp _ disp_add_unit_cat_ob_mor.
  Proof.
    refine (_ ,, _).
    - intros mx ηx ; cbn in *.
      rewrite !vassocl.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite lunitor_runitor_identity.
      rewrite !vassocr.
      rewrite runitor_rinvunitor.
      rewrite id2_left.
      apply idpath.
    - intros mx my mz f g ηx ηy ηz ηf ηg ; cbn in *.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      rewrite ηf.
      rewrite <- !rwhisker_vcomp.
      apply maponpaths_2.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite <- ηg.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition disp_add_unit_cat_data
    : disp_cat_data (end_bicat B).
  Proof.
    simple refine (_ ,, _).
    - exact disp_add_unit_cat_ob_mor.
    - exact disp_add_unit_cat_id_comp.
  Defined.

  Definition disp_add_unit
    : disp_bicat (end_bicat B).
  Proof.
    use disp_cell_unit_bicat.
    exact disp_add_unit_cat_data.
  Defined.

  Definition disp_univalent_2_1_disp_add_unit
    : disp_univalent_2_1 disp_add_unit.
  Proof.
    use disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply cellset_property.
  Qed.

  Definition disp_univalent_2_0_disp_add_unit
             (HB : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_add_unit.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - use total_is_univalent_2_1.
      + exact HB.
      + apply disp_univalent_2_1_disp_end.
    - intros ; apply cellset_property.
    - intro ; apply cellset_property.
    - intros ex ef eg pq.
      pose (p := maponpaths (λ z, runitor _ • z • runitor _) (pr1 pq)).
      cbn in p.
      rewrite lunitor_V_id_is_left_unit_V_id in p.
      rewrite !vassocr in p.
      rewrite !runitor_rinvunitor in p.
      rewrite !id2_left in p.
      rewrite !vassocl in p.
      rewrite rinvunitor_runitor in p.
      rewrite id2_right in p.
      rewrite vcomp_lunitor, vcomp_runitor in p.
      rewrite runitor_lunitor_identity in p.
      pose (q := maponpaths (λ z, linvunitor _ • z) p).
      cbn in q.
      rewrite !vassocr in q.
      rewrite !linvunitor_lunitor in q.
      rewrite !id2_left in q.
      exact q.
  Qed.

  Definition disp_univalent_2_disp_add_unit
             (HB : is_univalent_2_1 B)
    : disp_univalent_2 disp_add_unit.
  Proof.
    split.
    - apply disp_univalent_2_0_disp_add_unit.
      exact HB.
    - apply disp_univalent_2_1_disp_add_unit.
  Qed.

  Definition disp_add_mu_cat_ob_mor
    : disp_cat_ob_mor (end_bicat B).
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ mx, pr2 mx · pr2 mx ==> pr2 mx).
    - exact (λ mx my μx μy f,
             lassociator _ _ _
             • (pr2 f ▹ _)
             • rassociator _ _ _
             • (_ ◃ pr2 f)
             • lassociator _ _ _
             • (μx ▹ _)
             =
             (_ ◃ μy)
             • pr2 f).
  Defined.

  Definition disp_add_mu_cat_id_comp
    : disp_cat_id_comp _ disp_add_mu_cat_ob_mor.
  Proof.
    refine (_ ,, _).
    - intros mx μx ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rinvunitor_triangle.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
    - intros mx my mz mf mg μx μy μz μf μg ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !vassocl in μf.
      rewrite !vassocl in μg.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite <- μg.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      clear μg.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      refine (!_).
      etrans.
      {
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
      apply maponpaths.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
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
        rewrite <- μf.
        rewrite <- !rwhisker_vcomp.
        apply idpath.
      }
      clear μf.
      etrans.
      {
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
      apply maponpaths.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      apply rassociator_rassociator.
  Qed.

  Definition disp_add_mu_cat_data
    : disp_cat_data (end_bicat B).
  Proof.
    simple refine (_ ,, _).
    - exact disp_add_mu_cat_ob_mor.
    - exact disp_add_mu_cat_id_comp.
  Defined.

  Definition disp_add_mu
    : disp_bicat (end_bicat B).
  Proof.
    use disp_cell_unit_bicat.
    exact disp_add_mu_cat_data.
  Defined.

  Definition disp_univalent_2_1_disp_add_mu
    : disp_univalent_2_1 disp_add_mu.
  Proof.
    use disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply cellset_property.
  Qed.

  Definition disp_univalent_2_0_disp_add_mu
             (HB : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_add_mu.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - use total_is_univalent_2_1.
      + exact HB.
      + apply disp_univalent_2_1_disp_end.
    - intros ; apply cellset_property.
    - intro ; apply cellset_property.
    - intros ex ef eg pq.
      pose (p := pr1 pq).
      cbn in p.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp in p.
      rewrite !vassocl in p.
      use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
      rewrite <- !vcomp_lunitor.
      use (vcomp_rcancel (rinvunitor _)) ; [ is_iso | ].
      rewrite !vassocl.
      refine (_ @ p).
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition disp_univalent_2_disp_add_mu
             (HB : is_univalent_2_1 B)
    : disp_univalent_2 disp_add_mu.
  Proof.
    split.
    - apply disp_univalent_2_0_disp_add_mu.
      exact HB.
    - apply disp_univalent_2_1_disp_add_mu.
  Qed.

  Definition disp_mnd_data
    : disp_bicat B
    := sigma_bicat
         B
         _
         (disp_dirprod_bicat disp_add_unit disp_add_mu).

  Definition disp_2cells_isaprop_disp_mnd_data
    : disp_2cells_isaprop disp_mnd_data.
  Proof.
    use disp_2cells_isaprop_sigma.
    - apply disp_2cells_isaprop_end_bicat.
    - use disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_cell_unit_bicat.
  Qed.

  Definition disp_locally_sym_disp_mnd_data
    : disp_locally_sym disp_mnd_data.
  Proof.
    intros x y f g τ mx my mf mg mτ.
    simple refine ((_ ,, (tt ,, tt))) ; cbn.
    pose (p := pr1 mτ) ; cbn in p.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    exact (!p).
  Qed.

  Definition disp_locally_groupoid_disp_mnd_data
    : disp_locally_groupoid disp_mnd_data.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_disp_mnd_data.
    - apply disp_2cells_isaprop_disp_mnd_data.
  Defined.

  Definition disp_univalent_2_1_disp_mnd_data
    : disp_univalent_2_1 disp_mnd_data.
  Proof.
    use sigma_disp_univalent_2_1_with_props.
    - apply disp_2cells_isaprop_end_bicat.
    - use disp_2cells_isaprop_prod.
      + apply disp_2cells_isaprop_cell_unit_bicat.
      + apply disp_2cells_isaprop_cell_unit_bicat.
    - apply disp_univalent_2_1_disp_end.
    - use is_univalent_2_1_dirprod_bicat.
      + apply disp_univalent_2_1_disp_add_unit.
      + apply disp_univalent_2_1_disp_add_mu.
  Defined.

  Definition disp_univalent_2_0_disp_mnd_data
             (HB : is_univalent_2 B)
    : disp_univalent_2_0 disp_mnd_data.
  Proof.
    use sigma_disp_univalent_2_0_with_props.
    - exact HB.
    - apply disp_2cells_isaprop_end_bicat.
    - use disp_2cells_isaprop_prod.
      + apply disp_2cells_isaprop_cell_unit_bicat.
      + apply disp_2cells_isaprop_cell_unit_bicat.
    - apply disp_univalent_2_1_disp_end.
    - use is_univalent_2_1_dirprod_bicat.
      + apply disp_univalent_2_1_disp_add_unit.
      + apply disp_univalent_2_1_disp_add_mu.
    - apply disp_locally_groupoid_end_bicat.
    - use disp_locally_groupoid_prod.
      + apply disp_locally_groupoid_cell_unit_bicat.
      + apply disp_locally_groupoid_cell_unit_bicat.
    - apply disp_univalent_2_0_disp_end.
      exact (pr2 HB).
    - use is_univalent_2_0_dirprod_bicat.
      + use total_is_univalent_2_1.
        * exact (pr2 HB).
        * apply disp_univalent_2_1_disp_end.
      + apply disp_univalent_2_disp_add_unit.
        exact (pr2 HB).
      + apply disp_univalent_2_disp_add_mu.
        exact (pr2 HB).
  Defined.

  Definition disp_univalent_2_disp_mnd_data
             (HB : is_univalent_2 B)
    : disp_univalent_2 disp_mnd_data.
  Proof.
    split.
    - apply disp_univalent_2_0_disp_mnd_data.
      exact HB.
    - apply disp_univalent_2_1_disp_mnd_data.
  Defined.

  Definition mnd_data
    : bicat
    := total_bicat disp_mnd_data.

  Definition is_mnd
             (m : mnd_data)
    : UU
    := let X := pr1 m in
       let f := pr12 m in
       let η := pr122 m in
       let μ := pr222 m in
       (linvunitor f • (η ▹ f) • μ = id2 f)
       ×
       (rinvunitor f • (f ◃ η) • μ = id2 f)
       ×
       (rassociator _ _ _ • (f ◃ μ) • μ
        =
        (μ ▹ f) • μ).

  Definition isaprop_is_mnd
             (m : mnd_data)
    : isaprop (is_mnd m).
  Proof.
    repeat (apply isapropdirprod) ; apply cellset_property.
  Qed.

  Definition disp_mnd
    : disp_bicat B
    := sigma_bicat
         B
         _
         (disp_fullsubbicat _ is_mnd).

  Definition disp_2cells_isaprop_disp_mnd
    : disp_2cells_isaprop disp_mnd.
  Proof.
    use disp_2cells_isaprop_sigma.
    - apply disp_2cells_isaprop_disp_mnd_data.
    - apply disp_2cells_isaprop_fullsubbicat.
  Qed.

  Definition disp_locally_sym_disp_mnd
    : disp_locally_sym disp_mnd.
  Proof.
    intros x y f g τ mx my mf mg mτ.
    simple refine ((_ ,, (tt ,, tt)) ,, tt) ; cbn.
    pose (p := pr11 mτ) ; cbn in p.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    exact (!p).
  Qed.

  Definition disp_locally_groupoid_disp_mnd
    : disp_locally_groupoid disp_mnd.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_disp_mnd.
    - apply disp_2cells_isaprop_disp_mnd.
  Defined.

  Definition disp_univalent_2_1_disp_mnd
    : disp_univalent_2_1 disp_mnd.
  Proof.
    use sigma_disp_univalent_2_1_with_props.
    - apply disp_2cells_isaprop_disp_mnd_data.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_univalent_2_1_disp_mnd_data.
    - apply disp_fullsubbicat_univalent_2_1.
  Defined.

  Definition disp_univalent_2_0_disp_mnd
             (HB : is_univalent_2 B)
    : disp_univalent_2_0 disp_mnd.
  Proof.
    use sigma_disp_univalent_2_0_with_props.
    - exact HB.
    - apply disp_2cells_isaprop_disp_mnd_data.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_univalent_2_1_disp_mnd_data.
    - apply disp_fullsubbicat_univalent_2_1.
    - apply disp_locally_groupoid_disp_mnd_data.
    - apply disp_locally_groupoid_fullsubbicat.
    - apply disp_univalent_2_0_disp_mnd_data.
      exact HB.
    - use disp_univalent_2_0_fullsubbicat.
      + apply total_is_univalent_2.
        * apply disp_univalent_2_disp_mnd_data.
          exact HB.
        * exact HB.
      + intro.
        repeat (use isapropdirprod) ; apply cellset_property.
  Defined.

  Definition mnd
    : bicat
    := total_bicat disp_mnd.

  (**
   2. The univalence
   *)
  Definition is_univalent_2_1_mnd
             (HB : is_univalent_2_1 B)
    : is_univalent_2_1 mnd.
  Proof.
    apply total_is_univalent_2_1.
    - exact HB.
    - apply disp_univalent_2_1_disp_mnd.
  Defined.

  Definition is_univalent_2_0_mnd
             (HB : is_univalent_2 B)
    : is_univalent_2_0 mnd.
  Proof.
    apply total_is_univalent_2_0.
    - exact (pr1 HB).
    - apply disp_univalent_2_0_disp_mnd.
      exact HB.
  Defined.

  Definition is_univalent_2_mnd
             (HB : is_univalent_2 B)
    : is_univalent_2 mnd.
  Proof.
    split.
    - exact (is_univalent_2_0_mnd HB).
    - exact (is_univalent_2_1_mnd (pr2 HB)).
  Defined.
End Monad.

(**
 3. Projections and constructions
 *)
Section MonadProjections.
  Context {B : bicat}
          (m : mnd B).

  Definition ob_of_mnd
    : B
    := pr1 m.

  Definition endo_of_mnd
    : ob_of_mnd --> ob_of_mnd
    := pr112 m.

  Definition unit_of_mnd
    : id₁ _ ==> endo_of_mnd
    := pr1 (pr212 m).

  Definition mult_of_mnd
    : endo_of_mnd · endo_of_mnd ==> endo_of_mnd
    := pr2 (pr212 m).

  Definition mnd_unit_left
    : linvunitor _ • (unit_of_mnd ▹ _) • mult_of_mnd = id2 _
    := pr122 m.

  Definition mnd_unit_right
    : rinvunitor _ • (_ ◃ unit_of_mnd) • mult_of_mnd = id2 _
    := pr1 (pr222 m).

  Definition mnd_mult_assoc
    : rassociator _ _ _ • (_ ◃ mult_of_mnd) • mult_of_mnd
      =
      (mult_of_mnd ▹ _) • mult_of_mnd
    := pr2 (pr222 m).

  Definition mnd_mult_assoc'
    : (_ ◃ mult_of_mnd) • mult_of_mnd
      =
      lassociator _ _ _ • (mult_of_mnd ▹ _) • mult_of_mnd.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn.
    rewrite !vassocr.
    exact mnd_mult_assoc.
  Qed.
End MonadProjections.

Definition make_mnd_data
           {B : bicat}
           (x : B)
           (f : x --> x)
           (η : id₁ _ ==> f)
           (μ : f · f ==> f)
  : mnd_data B
  := x ,, (f ,, (η ,, μ)).

Definition make_mnd
           {B : bicat}
           (m : mnd_data B)
           (Hm : is_mnd B m)
  : mnd B
  := pr1 m ,, (pr2 m ,, Hm).

Section MonadMapProjections.
  Context {B : bicat}
          {m₁ m₂ : mnd B}
          (f : m₁ --> m₂).

  Definition mor_of_mnd_mor
    : ob_of_mnd m₁ --> ob_of_mnd m₂
    := pr1 f.

  Definition mnd_mor_endo
    : mor_of_mnd_mor · endo_of_mnd m₂ ==> endo_of_mnd m₁ · mor_of_mnd_mor
    := pr112 f.

  Definition mnd_mor_unit
    : linvunitor _ • (unit_of_mnd m₁ ▹ _)
      =
      rinvunitor _ • (_ ◃ unit_of_mnd m₂) • mnd_mor_endo
    := pr1 (pr212 f).

  Definition mnd_mor_mu
    : lassociator _ _ _
      • (mnd_mor_endo ▹ _)
      • rassociator _ _ _
      • (_ ◃ mnd_mor_endo)
      • lassociator _ _ _
      • (mult_of_mnd m₁ ▹ _)
      =
      (_ ◃ mult_of_mnd m₂)
      • mnd_mor_endo
    := pr2 (pr212 f).
End MonadMapProjections.

Definition mnd_mor_data
           {B : bicat}
           (m₁ m₂ : mnd B)
  : UU
  := ∑ (f : ob_of_mnd m₁ --> ob_of_mnd m₂),
     f · endo_of_mnd m₂
     ==>
     endo_of_mnd m₁ · f.

Definition make_mnd_mor_data
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : ob_of_mnd m₁ --> ob_of_mnd m₂)
           (f_e : f · endo_of_mnd m₂
                  ==>
                  endo_of_mnd m₁ · f)
  : mnd_mor_data m₁ m₂
  := f ,, f_e.

Definition mnd_mor_laws
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_mor_data m₁ m₂)
  : UU
  := (linvunitor _ • (unit_of_mnd m₁ ▹ _)
      =
      rinvunitor _ • (_ ◃ unit_of_mnd m₂) • (pr2 f))
     ×
     (lassociator _ _ _
      • (pr2 f ▹ _)
      • rassociator _ _ _
      • (_ ◃ pr2 f)
      • lassociator _ _ _
      • (mult_of_mnd m₁ ▹ _)
      =
      (_ ◃ mult_of_mnd m₂)
      • pr2 f).

Definition make_mnd_mor_laws
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_mor_data m₁ m₂)
           (fη : linvunitor _ • (unit_of_mnd m₁ ▹ _)
                 =
                 rinvunitor _ • (_ ◃ unit_of_mnd m₂) • pr2 f)
           (fμ : lassociator _ _ _
                 • (pr2 f ▹ _)
                 • rassociator _ _ _
                 • (_ ◃ pr2 f)
                 • lassociator _ _ _
                 • (mult_of_mnd m₁ ▹ _)
                 =
                 (_ ◃ mult_of_mnd m₂)
                 • pr2 f)
  : mnd_mor_laws f
  := fη ,, fμ.

Definition make_mnd_mor
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_mor_data m₁ m₂)
           (Hf : mnd_mor_laws f)
  : m₁ --> m₂
  := pr1 f ,, (pr2 f ,, Hf) ,, tt.

Section MonadCellProjections.
  Context {B : bicat}
          {m₁ m₂ : mnd B}
          {f₁ f₂ : m₁ --> m₂}
          (τ : f₁ ==> f₂).

  Definition cell_of_mnd_cell
    : mor_of_mnd_mor f₁ ==> mor_of_mnd_mor f₂
    := pr1 τ.

  Definition mnd_cell_endo
    : mnd_mor_endo f₁ • (_ ◃ cell_of_mnd_cell)
      =
      (cell_of_mnd_cell ▹ _) • mnd_mor_endo f₂
    := pr112 τ.
End MonadCellProjections.

Definition mnd_cell_data
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f₁ f₂ : m₁ --> m₂)
  : UU
  := mor_of_mnd_mor f₁ ==> mor_of_mnd_mor f₂.

Definition is_mnd_cell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : m₁ --> m₂}
           (τ : mnd_cell_data f₁ f₂)
  : UU
  := mnd_mor_endo f₁ • (_ ◃ τ)
     =
     (τ ▹ _) • mnd_mor_endo f₂.

Definition make_mnd_cell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : m₁ --> m₂}
           (τ : mnd_cell_data f₁ f₂)
           (τ_e : is_mnd_cell τ)
  : f₁ ==> f₂
  := τ ,, ((τ_e ,, (tt ,, tt)) ,, tt).

Definition eq_mnd_cell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : m₁ --> m₂}
           {τ₁ τ₂ : f₁ ==> f₂}
           (p : cell_of_mnd_cell τ₁ = cell_of_mnd_cell τ₂)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro ; simpl.
    apply isapropdirprod ; [ | apply isapropunit ].
    apply isapropdirprod ; [ apply cellset_property | ].
    apply isapropdirprod ; apply isapropunit.
  }
  exact p.
Qed.

(**
 4. Invertible 2-cells
 *)
Section IsInvertibleMndCell.
  Context {B : bicat}
          {m₁ m₂ : mnd B}
          {f₁ f₂ : m₁ --> m₂}
          {τ : f₁ ==> f₂}
          (Hτ : is_invertible_2cell (cell_of_mnd_cell τ)).

  Definition is_invertible_mnd_2cell_inverse
    : f₂ ==> f₁.
  Proof.
    use make_mnd_cell.
    - exact (Hτ^-1).
    - abstract
        (cbn ;
         use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
         rewrite !vassocr ;
         use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
         refine (!_) ;
         exact (mnd_cell_endo τ)).
  Defined.

  Definition is_invertible_mnd_2cell
    : is_invertible_2cell τ.
  Proof.
    use make_is_invertible_2cell.
    - exact is_invertible_mnd_2cell_inverse.
    - abstract
        (use eq_mnd_cell ; cbn ;
         apply vcomp_rinv).
    - abstract
        (use eq_mnd_cell ; cbn ;
         apply vcomp_linv).
  Defined.
End IsInvertibleMndCell.

Definition from_invertible_mnd_2cell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : m₁ --> m₂}
           {τ : f₁ ==> f₂}
           (Hτ : is_invertible_2cell τ)
  : is_invertible_2cell (cell_of_mnd_cell τ).
Proof.
  use make_is_invertible_2cell.
  - exact (pr1 (Hτ^-1)).
  - abstract
      (exact (maponpaths pr1 (vcomp_rinv Hτ))).
  - abstract
      (exact (maponpaths pr1 (vcomp_linv Hτ))).
Defined.

(**
 5. Equivalences of monads
 *)
Section ToEquivalence.
  Context {B : bicat}
          {x : B}
          {mx mx' : disp_mnd B x}
          (m₁ := x,, mx : mnd B)
          (m₂ := x,, mx' : mnd B)
          (Hl : mx -->[ id₁ x ] mx').

  Let l : m₁ --> m₂ := id₁ x ,, Hl.

  Context (Hγ : is_invertible_2cell (mnd_mor_endo l)).

  Definition to_equivalence_mnd_help_right_adj_data
    : mnd_mor_data m₂ m₁.
  Proof.
    use make_mnd_mor_data.
    - exact (id₁ x).
    - exact (lunitor _
             • rinvunitor _
             • Hγ^-1
             • lunitor _
             • rinvunitor _).
  Defined.

  Definition to_equivalence_mnd_help_right_adj_laws
    : mnd_mor_laws to_equivalence_mnd_help_right_adj_data.
  Proof.
    split.
    - cbn.
      rewrite !vassocl.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply maponpaths.
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
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      rewrite id2_left.
      apply maponpaths.
      do 2 (use vcomp_move_R_Mp ; [ is_iso | ]) ; cbn.
      rewrite linvunitor_natural.
      rewrite rinvunitor_natural.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
      rewrite lunitor_V_id_is_left_unit_V_id.
      refine (_ @ mnd_mor_unit l).
      rewrite <- lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      do 3 (use vcomp_move_L_Mp ; [ is_iso | ]) ; cbn.
      rewrite !vassocl.
      etrans.
      {
        do 13 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_runitor.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite linvunitor_natural.
        rewrite <- lwhisker_hcomp.
        rewrite !vassocl.
        apply maponpaths.
        exact (!(mnd_mor_mu l)).
      }
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            rewrite !vassocr.
            do 12 apply maponpaths_2.
            rewrite rwhisker_hcomp.
            rewrite <- triangle_r_inv.
            rewrite <- lwhisker_hcomp.
            apply idpath.
          }
          rewrite lwhisker_vcomp.
          rewrite linvunitor_lunitor.
          rewrite lwhisker_id2.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rinvunitor_triangle.
        rewrite rinvunitor_runitor.
        rewrite id2_left.
        rewrite linvunitor_assoc.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      cbn.
      rewrite !vassocr.
      rewrite !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        do 2 apply maponpaths_2.
        apply maponpaths.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lunitor_linvunitor.
            apply id2_left.
          }
          apply vcomp_linv.
        }
        apply id2_right.
      }
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      refine (_ @ id2_right _).
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_linvunitor.
        apply id2_left.
      }
      apply vcomp_linv.
  Qed.

  Definition to_equivalence_mnd_help_right_adj
    : m₂ --> m₁.
  Proof.
    use make_mnd_mor.
    - exact to_equivalence_mnd_help_right_adj_data.
    - exact to_equivalence_mnd_help_right_adj_laws.
  Defined.

  Definition to_equivalence_mnd_help_equiv_unit_data
    : mnd_cell_data
        (id₁ m₁)
        (l · to_equivalence_mnd_help_right_adj)
    := linvunitor _.

  Definition to_equivalence_mnd_help_equiv_unit_is_mnd_cell
    : is_mnd_cell to_equivalence_mnd_help_equiv_unit_data.
  Proof.
    unfold is_mnd_cell, to_equivalence_mnd_help_equiv_unit_data ; cbn.
    rewrite !vassocr.
    refine (!_).
    rewrite <- linvunitor_assoc.
    rewrite lwhisker_hcomp.
    rewrite <- linvunitor_natural.
    rewrite !vassocl.
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    etrans.
    {
      do 6 apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_linvunitor.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    }
    do 2 apply maponpaths.
    rewrite <- rinvunitor_triangle.
    rewrite !vassocl.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    rewrite lunitor_V_id_is_left_unit_V_id.
    apply idpath.
  Qed.

  Definition to_equivalence_mnd_help_equiv_unit
    : id₁ m₁ ==> l · to_equivalence_mnd_help_right_adj.
  Proof.
    use make_mnd_cell.
    - exact to_equivalence_mnd_help_equiv_unit_data.
    - exact to_equivalence_mnd_help_equiv_unit_is_mnd_cell.
  Defined.

  Definition to_equivalence_mnd_help_equiv_counit_data
    : mnd_cell_data
        (to_equivalence_mnd_help_right_adj · l)
        (id₁ m₂)
    := lunitor _.

  Definition to_equivalence_mnd_help_equiv_counit_is_mnd_cell
    : is_mnd_cell to_equivalence_mnd_help_equiv_counit_data.
  Proof.
    unfold is_mnd_cell, to_equivalence_mnd_help_equiv_counit_data ; cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite <- lunitor_triangle.
    rewrite !vassocr.
    rewrite rassociator_lassociator.
    rewrite id2_left.
    rewrite !vassocl.
    apply maponpaths.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite !rwhisker_vcomp.
    use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
    rewrite !vassocl.
    rewrite vcomp_runitor.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite runitor_rinvunitor.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite vcomp_rinv.
    apply id2_left.
  Qed.

  Definition to_equivalence_mnd_help_equiv_counit
    : to_equivalence_mnd_help_right_adj · l ==> id₁ m₂.
  Proof.
    use make_mnd_cell.
    - exact to_equivalence_mnd_help_equiv_counit_data.
    - exact to_equivalence_mnd_help_equiv_counit_is_mnd_cell.
  Defined.

  Definition to_equivalence_mnd_help_equiv_data
    : left_adjoint_data l
    := to_equivalence_mnd_help_right_adj
       ,,
       (to_equivalence_mnd_help_equiv_unit
       ,,
       to_equivalence_mnd_help_equiv_counit).

  Definition to_equivalence_mnd_help_equiv_axioms
    : left_equivalence_axioms to_equivalence_mnd_help_equiv_data.
  Proof.
    split ; use is_invertible_mnd_2cell ; cbn.
    - unfold to_equivalence_mnd_help_equiv_unit_data.
      is_iso.
    - unfold to_equivalence_mnd_help_equiv_counit_data.
      is_iso.
  Defined.

  Definition to_equivalence_mnd_help_equiv
    : left_equivalence l
    := to_equivalence_mnd_help_equiv_data
       ,,
       to_equivalence_mnd_help_equiv_axioms.
End ToEquivalence.

Definition to_equivalence_mnd_help
           {B : bicat}
           (HB : is_univalent_2_0 B)
           {x y : B}
           (l : adjoint_equivalence x y)
           {mx : disp_mnd B x}
           {my : disp_mnd B y}
           (m₁ := x ,, mx : mnd B)
           (m₂ := y ,, my : mnd B)
           (Hl : mx -->[ l ] my)
           (ml := pr1 l ,, Hl : m₁ --> m₂)
           (Hγ : is_invertible_2cell (mnd_mor_endo ml))
  : left_adjoint_equivalence ml.
Proof.
  revert x y l mx my m₁ m₂ Hl ml Hγ.
  use (J_2_0 HB).
  intros x mx mx' m₁ m₂ Hl ml Hγ.
  use equiv_to_adjequiv.
  exact (to_equivalence_mnd_help_equiv Hl Hγ).
Defined.

Definition to_equivalence_mnd
           {B : bicat}
           (HB : is_univalent_2_0 B)
           {m₁ m₂ : mnd B}
           (l : m₁ --> m₂)
           (Hl : left_adjoint_equivalence (pr1 l))
           (Hγ : is_invertible_2cell (mnd_mor_endo l))
  : left_adjoint_equivalence l.
Proof.
  exact (to_equivalence_mnd_help
           HB
           (pr1 l ,, Hl)
           (pr2 l)
           Hγ).
Defined.

(**
 6. Underlying pseudofunctor
 *)
Definition und_mnd
           (B : bicat)
  : psfunctor (mnd B) B
  := pr1_psfunctor _.
