(* ******************************************************************************* *)
(** * Representable pseudofunctor, pseudotransformation, and modifications
    Niccolò Veltri, Niels van der Weide
    April 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OpMorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section RepresentableFunctor.

Context {C : bicat}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

Definition pspsh := psfunctor (op1_bicat C) bicat_of_cats.

Definition representable_data_cat (X Y : C) : univalent_category
  := univ_hom C_is_univalent_2_1 Y X.

Definition representable_data_fun (X Y Z : C) (f : op1_bicat C ⟦ Y, Z ⟧)
  : bicat_of_cats ⟦ representable_data_cat X Y, representable_data_cat X Z ⟧.
Proof.
  simpl in f.
  use mk_functor.
  - use mk_functor_data.
    + intro g.
      exact (f · g).
    + intros g h.
      exact (lwhisker f).
  - split.
    + exact (lwhisker_id2 f).
    + intros g h k η φ.
      exact (! (lwhisker_vcomp f η φ)).
Defined.

Definition representable_data_nat (X Y Z : C) (f g : op1_bicat C ⟦ Y, Z ⟧)
  : f ==> g → representable_data_fun X Y Z f ==> representable_data_fun X Y Z g.
Proof.
  intro η.
  use mk_nat_trans.
  - intro h.
    exact (rwhisker h η).
  - intros h k φ.
    exact (! (@vcomp_whisker C Z Y X f g h k η φ)).
Defined.

Definition representable_data (X : C) : psfunctor_data (op1_bicat C) bicat_of_cats.
Proof.
  use mk_psfunctor_data.
  - exact (representable_data_cat X).
  - exact (representable_data_fun X).
  - exact (representable_data_nat X).
  - intro Y.
    use mk_nat_trans.
    + exact linvunitor.
    + abstract (intros f g η ;
                simpl in * ;
                rewrite lwhisker_hcomp ;
                apply linvunitor_natural).
  - intros Y Z W f g.
    use mk_nat_trans.
    + intro h. simpl.
      cbn in *.
      apply lassociator.
    + intros h k η.
      simpl.
      apply lwhisker_lwhisker.
Defined.

Definition representable_laws (X : C) : psfunctor_laws (representable_data X).
Proof.
  repeat split; cbn.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      apply id2_rwhisker.
  - intros Y Z f g h η φ.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro k. cbn.
      symmetry.
      apply rwhisker_vcomp.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      rewrite <- vassocr.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      symmetry.
      apply lwhisker_id2.
  - intros Y Z f.
    use nat_trans_eq.
    + exact (pr2 C Z X).
    + intro g. cbn.
      rewrite linvunitor_assoc.
      refine (!(_@ _)).
      {
        apply maponpaths_2.
        rewrite <- vassocr.
        rewrite rassociator_lassociator.
        apply id2_right.
      }
      rewrite rwhisker_vcomp.
      rewrite linvunitor_lunitor.
      apply id2_rwhisker.
  - intros Y Z W V f g h.
    use nat_trans_eq.
    + exact (pr2 C V X).
    + intro k.
      cbn in *.
      rewrite id2_left.
      pose (pentagon_2 k f g h) as p.
      rewrite lwhisker_hcomp,rwhisker_hcomp.
      rewrite <- vassocr.
      exact (! p).
  - intros Y Z W f g h η.
    use nat_trans_eq.
    + exact (pr2 C W X).
    + intro k.
      cbn in *.
      apply rwhisker_rwhisker.
  - intros Y Z W f g h η.
    use nat_trans_eq.
    + exact (pr2 C W X).
    + intro k.
      cbn in *.
      symmetry.
      apply rwhisker_lwhisker.
Qed.


Definition representable_invertible_cells (X : C) : invertible_cells (representable_data X).
Proof.
  split.
  - intro Y.
    use is_nat_iso_to_is_invertible_2cell.
    intro f.
    simpl.
    apply is_inv2cell_to_is_iso.
    is_iso.
  - intros Y Z W f g.
    use is_nat_iso_to_is_invertible_2cell.
    intro h.
    simpl.
    apply is_inv2cell_to_is_iso.
    is_iso.
Defined.

Definition representable (X : C) : pspsh.
Proof.
  use mk_psfunctor.
  - exact (representable_data X).
  - exact (representable_laws X).
  - exact (representable_invertible_cells X).
Defined.

End RepresentableFunctor.

Section RepresentableTransformation.

Context {C : bicat}{X Y : C}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C) (f : X --> Y).

Definition representable1_data :
  pstrans_data (representable C_is_univalent_2_1 X) (representable C_is_univalent_2_1 Y).
Proof.
  use mk_pstrans_data.
  - intro Z.
    cbn.
    use mk_functor.
    + use mk_functor_data.
      -- intro g.
         exact (g · f).
      -- intros g h η.
         exact (rwhisker f η).
    + split.
      -- intro g.
         apply id2_rwhisker.
      -- intros g h k η φ.
         symmetry.
         apply rwhisker_vcomp.
  - intros Z W h.
    cbn.
    use mk_invertible_2cell.
    + use mk_nat_trans.
      -- intro k.
         apply lassociator.
      -- intros k l η.
         cbn in *.
         apply rwhisker_lwhisker.
    + use is_nat_iso_to_is_invertible_2cell.
      intro g.
      apply is_inv2cell_to_is_iso.
      simpl.
      is_iso.
Defined.

Definition representable1_is_pstrans : is_pstrans representable1_data.
Proof.
  repeat (apply tpair).
  - intros Z W g h η.
    use nat_trans_eq.
    { exact (pr2 C W Y). }
    intro k.
    simpl.
    symmetry.
    apply rwhisker_rwhisker.
  - intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro h.
    cbn in *.
    rewrite !id2_left.
    rewrite linvunitor_assoc.
    rewrite <- vassocr.
    rewrite rassociator_lassociator.
    apply id2_right.
  - intros Z W V g h.
    use nat_trans_eq.
    { exact (pr2 C V Y). }
    intro k.
    cbn in *.
    rewrite id2_left , ! id2_right.
    symmetry.
    apply lassociator_lassociator.
Qed.

Definition representable1 :
  pstrans (representable C_is_univalent_2_1 X) (representable C_is_univalent_2_1 Y).
Proof.
  use mk_pstrans.
  - exact representable1_data.
  - exact representable1_is_pstrans.
Defined.

End RepresentableTransformation.

Section RepresentableModification.

Context {C : bicat}{X Y : C}{f g : X --> Y}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C) (η : f ==> g).

Definition representable2_data
  : modification_data (representable1 C_is_univalent_2_1 f)
                      (representable1 C_is_univalent_2_1 g).
Proof.
  intro Z.
  use mk_nat_trans.
  - intro h.
    simpl.
    exact (h ◃ η).
  - intros h k φ.
    simpl.
    apply vcomp_whisker.
Defined.

Definition representable2_is_modification
  : is_modification (σ := representable1 C_is_univalent_2_1 f) representable2_data.
Proof.
  intros Z W h.
  use nat_trans_eq.
  { exact (pr2 C W Y). }
  intro k.
  cbn in *.
  symmetry.
  apply lwhisker_lwhisker.
Qed.

Definition representable2 :
  modification (representable1 C_is_univalent_2_1 f) (representable1 C_is_univalent_2_1 g).
Proof.
  use mk_modification.
  - apply representable2_data.
  - apply representable2_is_modification.
Defined.

End RepresentableModification.