Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.LaxTransformation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.

Local Open Scope cat.

Section Add2Cell.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Local Notation E := (total_bicat D).
  Local Notation F := (pr1_psfunctor D).

  Variable (S : psfunctor E E)
           (l r : pstrans S (ps_id_functor E)).

  Definition add_cell_disp_cat_data : disp_cat_ob_mor E.
  Proof.
    use tpair.
    - exact (λ X, #F (l X) ==> #F (r X)).
    - exact (λ X Y α β f,
             ((psfunctor_comp F (l X) f)^-1)
               • (α ▹ #F f)
               • psfunctor_comp F (r X) f
               • ##F (laxnaturality_of r f)
             =
             (##F (laxnaturality_of l f))
               • (psfunctor_comp F (#S f) (l Y))^-1
               • (#F(#S f) ◃ β)
               • psfunctor_comp F (#S f) (r Y)).
  Defined.

  Definition add_cell_disp_cat_laws : disp_cat_id_comp E add_cell_disp_cat_data.
  Proof.
    split.
    - intros x xx ; cbn.
      rewrite !id2_left, !id2_right.
      pose (maponpaths pr1 (laxtrans_id_alt l x)) as p.
      cbn in p.
      rewrite p ; clear p.
      pose (maponpaths pr1 (laxtrans_id_alt r x)) as p.
      cbn in p.
      rewrite p ; clear p.
      rewrite !lwhisker_id2, !id2_left.
      rewrite !vassocr.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_hcomp.
      rewrite vcomp_whisker.
      reflexivity.
    - intros x y z f g xx yy zz Hf Hg.
      pose (maponpaths pr1 (laxtrans_comp_alt l f g)) as pl.
      pose (maponpaths pr1 (laxtrans_comp_alt r f g)) as pr.
      cbn in *.
      rewrite pl, pr ; clear pl pr.
      rewrite !id2_left, !id2_right in Hf.
      rewrite !id2_left, !id2_right in Hg.
      rewrite !id2_left, !id2_right.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_2.
        apply maponpaths.
        apply Hf.
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite lwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        apply Hg.
      }
      rewrite <- lwhisker_vcomp.
      reflexivity.
  Qed.

  Definition add_cell_disp_cat : disp_bicat E.
  Proof.
    use disp_cell_unit_bicat.
    use tpair.
    - exact add_cell_disp_cat_data.
    - exact add_cell_disp_cat_laws.
  Defined.

  Definition add_cell_disp_cat_locally_univalent
    : disp_locally_univalent add_cell_disp_cat.
  Proof.
    apply disp_cell_unit_bicat_locally_univalent.
    intros.
    simpl.
    apply C.
  Defined.

  Definition add_cell_disp_cat_univalent_2_0
             (HC : is_univalent_2_1 C)
             (HD : disp_locally_univalent D)
    : disp_univalent_2_0 add_cell_disp_cat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - intro ; intros.
      apply isasetaprop.
      apply isapropunit.
    - apply total_is_locally_univalent.
      + exact HC.
      + exact HD.
    - intros.
      apply C.
    - intros x xx yy.
      use isweqimplimpl.
      + intros p.
        induction p as [p q].
        cbn ; unfold idfun.
        cbn in p, q.
        rewrite !id2_left, id2_right in p.
        rewrite (laxtrans_id_alt l), (laxtrans_id_alt r) in p.
        cbn in p.
        rewrite !lwhisker_id2 in p.
        rewrite !id2_left, !id2_right in p.
        rewrite !vassocr in p.
        rewrite vcomp_runitor in p.
        rewrite !vassocl in p.
        pose (vcomp_lcancel _ (is_invertible_2cell_runitor _) p) as p'.
        use (vcomp_rcancel (linvunitor (pr1 (r x)))).
        { is_iso. }
        use (vcomp_rcancel (pr1 (laxfunctor_id S x) ▹ pr1 (r x))).
        { is_iso.
          use tpair.
          - apply (pr1(pr2 S) x).
          - split.
            + exact (base_paths _ _ (pr1(pr2(pr1(pr2 S) x)))).
            + exact (base_paths _ _ (pr2(pr2(pr1(pr2 S) x)))).
        }
        rewrite !vassocl.
        refine (p' @ _).
        rewrite vcomp_whisker.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lwhisker_hcomp.
        refine (!(linvunitor_natural _)).
      + apply C.
      + apply isapropdirprod ; apply C.
  Defined.
End Add2Cell.