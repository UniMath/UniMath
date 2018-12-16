(**
Given is a displayed bicategory on C. Then we have a total category E of which the objects are objects in C with some additional structure.
In this file, we give a method for adding 2-cells to the structure, which represents an equation on the structure in the total category.
The equation has two endpoints, l and r. These are given as natural maps in the underlying bicategory.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.

Local Open Scope cat.

Section Add2Cell.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Local Notation E := (total_bicat D).
  Local Notation F := (pr1_psfunctor D).

  Variable (S : psfunctor C C)
           (l r : pstrans (@ps_comp E C C S F)
                          (@ps_comp E C C (ps_id_functor C) F)).

  Definition add_cell_disp_cat_data : disp_cat_ob_mor E.
  Proof.
    use tpair.
    - exact (λ X, l X ==> r X).
    - exact (λ X Y α β f,
             (α ▹ #F f)
               • psnaturality_of r f
             =
             (psnaturality_of l f)
               • (#S(#F f) ◃ β)).
  Defined.

  Definition add_cell_disp_cat_laws : disp_cat_id_comp E add_cell_disp_cat_data.
  Proof.
    split.
    - intros x xx ; cbn.
      pose (pstrans_id_alt l x) as p.
      cbn in p ; rewrite p ; clear p.
      pose (pstrans_id_alt r x) as p.
      cbn in p ; rewrite p ; clear p.
      rewrite !id2_right, !lwhisker_id2, !id2_left.
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
    - intros x y z f g xx yy zz Hf Hg ; cbn.
      pose (pstrans_comp_alt l f g) as pl.
      pose (pstrans_comp_alt r f g) as pr.
      cbn in pl, pr ; rewrite pl, pr ; clear pl pr.
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
    apply C.
  Defined.

  Definition add_cell_disp_cat_univalent_2_0
             (HC : is_univalent_2_1 C)
             (HD : disp_locally_univalent D)
    : disp_univalent_2_0 add_cell_disp_cat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - apply total_is_locally_univalent.
      + exact HC.
      + exact HD.
    - intros.
      apply C.
    - intros x xx yy.
      simpl in *.
      apply C.
    - intros x xx yy.
      intros p.
      induction p as [p q].
      cbn ; unfold idfun.
      cbn in p, q.
      pose (pstrans_id_alt l) as pl.
      cbn in pl ; rewrite pl in p ; clear pl.
      pose (pstrans_id_alt r) as pr.
      cbn in pr ; rewrite pr in p ; clear pr.
      cbn in p.
      rewrite !id2_right in p.
      rewrite !lwhisker_id2 in p.
      rewrite !id2_left in p.
      rewrite !vassocr in p.
      rewrite vcomp_runitor in p.
      rewrite !vassocl in p.
      pose (vcomp_lcancel _ (is_invertible_2cell_runitor _) p) as p'.
      use (vcomp_rcancel (linvunitor (r x))).
      { is_iso. }
      use (vcomp_rcancel  (psfunctor_id S (pr1 x) ▹ r x)).
      { is_iso.
        exact (psfunctor_id S (pr1 x)).
      }
      rewrite !vassocl.
      rewrite psfunctor_id2, id2_right in p'.
      refine (p' @ _).
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_hcomp.
      exact (!(linvunitor_natural _)).
  Defined.
End Add2Cell.