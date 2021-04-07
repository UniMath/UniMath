(**
Given is a displayed bicategory on C. Then we have a total category E of which the objects are objects in C with some additional structure.
In this file, we give a method for adding 2-cells to the structure, which represents an equation on the structure in the total category.
The equation has two endpoints, l and r. These are given as natural maps in the underlying bicategory.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.

Local Open Scope cat.

Section Add2Cell.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Local Notation E := (total_bicat D).
  Local Notation F := (pr1_psfunctor D).

  Variable (S T : psfunctor C C)
           (l r : pstrans
                    (@comp_psfunctor E C C S F)
                    (@comp_psfunctor E C C T F)).

  Definition add_cell_disp_cat_data : disp_cat_ob_mor E.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ X, l X ==> r X).
    - exact (λ X Y α β f,
             (α ▹ #T(#F f))
               • psnaturality_of r f
             =
             (psnaturality_of l f)
               • (#S(#F f) ◃ β)).
  Defined.

  Definition add_cell_disp_cat_id_comp : disp_cat_id_comp E add_cell_disp_cat_data.
  Proof.
    split.
    - intros x xx.
      pose (pstrans_id_alt l x) as p.
      simpl.
      cbn in p.
      rewrite !psfunctor_id2 in p.
      rewrite id2_left, id2_right in p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      clear p.
      refine (!_).
      pose (pstrans_id_alt r x) as p.
      cbn in p.
      rewrite !psfunctor_id2 in p.
      rewrite id2_left, id2_right in p.
      etrans.
      {
        apply maponpaths.
        exact p.
      }
      clear p.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      apply idpath.
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
    - exact add_cell_disp_cat_id_comp.
  Defined.

  Definition add_cell_disp_cat_univalent_2_1
    : disp_univalent_2_1 add_cell_disp_cat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply C.
  Defined.

  Definition add_cell_disp_cat_univalent_2_0
             (HC : is_univalent_2_1 C)
             (HD : disp_univalent_2_1 D)
    : disp_univalent_2_0 add_cell_disp_cat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - apply total_is_univalent_2_1.
      + exact HC.
      + exact HD.
    - intros.
      apply C.
    - intros x xx yy.
      simpl in *.
      apply C.
    - abstract
        (intros x xx yy;
         intros p;
         induction p as [p q];
         cbn;
         cbn in p, q;
         pose (pstrans_id_alt l) as pl;
         cbn in pl ; rewrite pl in p ; clear pl;
         pose (pstrans_id_alt r) as pr;
         cbn in pr ; rewrite pr in p ; clear pr;
         cbn in p;
         rewrite !psfunctor_id2 in p;
         rewrite !id2_right, !id2_left in p;
         rewrite !vassocr in p;
         rewrite vcomp_whisker in p;
         rewrite !vassocl in p;
         assert (is_invertible_2cell (l x ◃ ((pr122 T) (pr1 x)) ^-1)) as H;
         try is_iso ;
         pose (vcomp_lcancel _ H p) as p';
         rewrite !vassocr in p';
         rewrite vcomp_runitor in p';
         rewrite !vassocl in p';
         pose (vcomp_lcancel _ (is_invertible_2cell_runitor _) p') as p'';
         use (vcomp_rcancel (linvunitor (r x))) ; try is_iso;
         use (vcomp_rcancel  (psfunctor_id S (pr1 x) ▹ r x))
         ; try (is_iso ; exact (psfunctor_id S (pr1 x)));
         rewrite !vassocl;
         refine (p'' @ _);
         rewrite vcomp_whisker;
         rewrite !vassocr;
         apply maponpaths_2;
         rewrite lwhisker_hcomp;
         exact (!(linvunitor_natural _))).
  Defined.

  Definition add_cell_disp_cat_univalent_2
             (HC : is_univalent_2_1 C)
             (HD : disp_univalent_2_1 D)
    : disp_univalent_2 add_cell_disp_cat.
  Proof.
    apply make_disp_univalent_2.
    - apply add_cell_disp_cat_univalent_2_0; assumption.
    - apply add_cell_disp_cat_univalent_2_1.
  Defined.

  Definition disp_2cells_isaprop_add_cell
    : disp_2cells_isaprop add_cell_disp_cat.
  Proof.
    intro; intros; exact isapropunit.
  Qed.

  Definition disp_locally_groupoid_add_cell
    : disp_locally_groupoid add_cell_disp_cat.
  Proof.
    use make_disp_locally_groupoid.
    - intro; intros. exact tt.
    - exact disp_2cells_isaprop_add_cell.
  Qed.

End Add2Cell.
