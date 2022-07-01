(** **********************************************************

Ralph Matthes

2022
*)

(** **********************************************************

Contents :

- constructs a displayed monoidal category that is displayed over a cartesian monoidal category with the displayed tensor and displayed unit coming from displayed binary products and displayed terminal objects

 ************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.

Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.
Import MonoidalNotations.
Import DisplayedBifunctorNotations.

Section FixADisplayedCategory.

  Context {C : category} (CP : BinProducts C) (terminal : Terminal C)
    (D : disp_cat C) (dP : dispBinProducts D CP) (dterminal : dispTerminal D terminal).

  Local Definition M : monoidal C := cartesianmonoidalcat C CP terminal.

  Definition DCM_tensor_data : disp_bifunctor_data M D D D.
  Proof.
    use make_disp_bifunctor_data.
    - intros c d cc dd.
      exact (dispBinProductObject D (CP c d) (dP c d cc dd)).
    - intros c d1 d2 g cc dd1 dd2 gg.
      exact (dispBinProductOfArrows _ _ _ (id_disp cc) gg).
    - intros c1 c2 d f cc1 cc2 dd ff.
      exact (dispBinProductOfArrows _ _ _ ff (id_disp dd)).
  Defined.

  Definition DCM_tensor_laws : is_disp_bifunctor DCM_tensor_data.
  Proof.
    red; repeat split; red; intros.
    - cbn. unfold dispBinProductOfArrows. apply pathsinv0. apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_left_disp.
        rewrite id_right_disp.
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        rewrite transport_f_b.
        apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_left_disp.
        rewrite id_right_disp.
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        rewrite transport_f_b.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
    - cbn. unfold dispBinProductOfArrows. apply pathsinv0. apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_left_disp.
        rewrite id_right_disp.
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        rewrite transport_f_b.
        apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_left_disp.
        rewrite id_right_disp.
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        rewrite transport_f_b.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
    - cbn. unfold dispBinProductOfArrows. apply pathsinv0. apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_right_disp.
        rewrite transport_b_b.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        etrans.
        2: { apply maponpaths. apply maponpaths.
             apply pathsinv0, dispBinProductPr1Commutes. }
        apply transportf_comp_lemma.
        rewrite id_right_disp.
        rewrite transport_b_b.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, dispBinProductPr1Commutes. }
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_right_disp.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        etrans.
        2: { apply maponpaths. apply maponpaths.
             apply pathsinv0, dispBinProductPr2Commutes. }
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        apply transportf_comp_lemma.
        etrans.
        2: { rewrite assoc_disp. apply idpath. }
        match goal with | [ |- _ = transportb _ _ (?auxH1 ;; gg2) ] => set (aux1 := auxH1) end.
        assert (H: aux1 = transportb (mor_disp (dispBinProductObject D (CP x y1) (dP x y1 xx yy1)) yy2)
           (BinProductPr2Commutes C x y2 (CP x y2) (BinProductObject C (CP x y1))
              (BinProductPr1 C (CP x y1) · identity x) (BinProductPr2 C (CP x y1) · g1))
           (dispBinProductPr2 D (CP x y1) (dP x y1 xx yy1) ;; gg1)).
        { apply dispBinProductPr2Commutes. }
        apply transportf_comp_lemma.
        unfold transportb in H.
        etrans.
        2: { apply pathsinv0, (cancel_postcomposition_disp gg2 H). }
        clear aux1 H.
        rewrite assoc_disp_var.
        rewrite transport_f_f.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
    - cbn. unfold dispBinProductOfArrows. apply pathsinv0. apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite id_right_disp.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        etrans.
        2: { apply maponpaths. apply maponpaths.
             apply pathsinv0, dispBinProductPr1Commutes. }
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0,  mor_disp_transportf_prewhisker. }
        etrans.
        2: { rewrite assoc_disp. apply idpath. }
        unfold transportb.
        rewrite transport_f_f.
        match goal with | [ |- _ = transportf _ _ (?auxH1 ;; ff2) ] => set (aux1 := auxH1) end.
        assert (H: aux1 = transportb (mor_disp (dispBinProductObject D (CP x1 y) (dP x1 y xx1 yy)) xx2)
           (BinProductPr1Commutes C x2 y (CP x2 y) (BinProductObject C (CP x1 y))
              (BinProductPr1 C (CP x1 y) · f1) (BinProductPr2 C (CP x1 y) · identity y))
           (dispBinProductPr1 D (CP x1 y) (dP x1 y xx1 yy) ;; ff1)).
        { apply dispBinProductPr1Commutes. }
        apply transportf_comp_lemma.
        unfold transportb in H.
        etrans.
        2: { apply pathsinv0, (cancel_postcomposition_disp ff2 H). }
        clear aux1 H.
        rewrite assoc_disp_var.
        rewrite transport_f_f.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        do 2 rewrite id_right_disp.
        rewrite transport_b_b.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        etrans.
        2: { apply maponpaths. apply maponpaths.
             apply pathsinv0, dispBinProductPr2Commutes. }
        apply transportf_comp_lemma.
        rewrite transport_b_b.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, dispBinProductPr2Commutes. }
        rewrite transport_b_b.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset;
          try apply homset_property; apply idpath.
    - cbn. unfold dispfunctoronmorphisms1, dispfunctoronmorphisms2,
        disp_leftwhiskering_on_morphisms, disp_rightwhiskering_on_morphisms.
      cbn. do 2 rewrite dispBinProductOfArrows_comp.
      do 2 rewrite id_left_disp.
      do 2 rewrite id_right_disp.
      rewrite transport_b_b.
      apply transportf_comp_lemma.
      unfold dispBinProductOfArrows. apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        etrans.
        { apply maponpaths.
          apply dispBinProductPr1Commutes. }
        rewrite transport_f_b.
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        etrans.
        { apply maponpaths.
          apply mor_disp_transportf_prewhisker. }
        rewrite transport_f_f.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        etrans.
        { apply maponpaths.
          apply dispBinProductPr2Commutes. }
        rewrite transport_f_b.
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        etrans.
        { apply maponpaths.
          apply mor_disp_transportf_prewhisker. }
        rewrite transport_f_f.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
  Qed.

  Definition DCM_tensor : disp_tensor D M.
  Proof.
    use make_disp_bifunctor.
    - exact DCM_tensor_data.
    - exact DCM_tensor_laws.
  Defined.

  Definition DCM_unit : D I_{ M} := dispTerminalObject _ dterminal.

  Definition DCM_leftunitor_data : disp_leftunitor_data DCM_tensor DCM_unit.
  Proof.
    red; intros. apply dispBinProductPr2.
  Defined.

  Definition DCM_leftunitorinv_data : disp_leftunitorinv_data DCM_tensor DCM_unit.
  Proof.
    red; intros. apply dispBinProductArrow.
    - apply dispTerminalArrow.
    - apply id_disp.
  Defined.

  Definition DCM_rightunitor_data : disp_rightunitor_data DCM_tensor DCM_unit.
  Proof.
    red; intros. apply dispBinProductPr1.
  Defined.

  Definition DCM_rightunitorinv_data : disp_rightunitorinv_data DCM_tensor DCM_unit.
  Proof.
    red; intros. apply dispBinProductArrow.
    - apply id_disp.
    - apply dispTerminalArrow.
  Defined.

  Definition DCM_associator_data : disp_associator_data DCM_tensor.
  Proof.
    red; intros.
    apply dispBinProductArrow.
    + use comp_disp.
      2: {apply dispBinProductPr1. }
      apply dispBinProductPr1.
    + apply dispBinProductArrow.
      * use comp_disp.
        2: {apply dispBinProductPr1. }
        apply dispBinProductPr2.
      * apply dispBinProductPr2.
  Defined.

  Definition DCM_associatorinv_data : disp_associatorinv_data DCM_tensor.
  Proof.
    red; intros.
    apply dispBinProductArrow.
    + apply dispBinProductArrow.
      * apply dispBinProductPr1.
      * use comp_disp.
        2: {apply dispBinProductPr2. }
        apply dispBinProductPr1.
    + use comp_disp.
      2: {apply dispBinProductPr2. }
      apply dispBinProductPr2.
  Defined.

  Definition DCM_data : disp_monoidal_data D M.
  Proof.
    exists DCM_tensor. exists DCM_unit.
    repeat split.
    - exact DCM_leftunitor_data.
    - exact DCM_leftunitorinv_data.
    - exact DCM_rightunitor_data.
    - exact DCM_rightunitorinv_data.
    - exact DCM_associator_data.
    - exact DCM_associatorinv_data.
  Defined.

  Lemma DCM_leftunitor_law : disp_leftunitor_law DCM_leftunitor_data DCM_leftunitorinv_data.
  Proof.
    split; [| split]; try red; intros.
    - cbn.
      etrans.
      { apply dispBinProductOfArrowsPr2. }
      unfold DCM_leftunitor_data.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - cbn. unfold DCM_leftunitorinv_data, DCM_leftunitor_data.
      rewrite dispBinProductPr2Commutes.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - cbn. unfold DCM_leftunitorinv_data, DCM_leftunitor_data.
      apply pathsinv0.
      etrans.
      2: { apply dispBinProduct_endo_is_identity.
           + apply dispTerminalArrowEq.
           + rewrite assoc_disp_var.
             rewrite dispBinProductPr2Commutes.
             apply pathsinv0, transportf_comp_lemma.
             etrans.
             2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
             rewrite id_right_disp.
             rewrite transport_f_b.
             apply transportf_comp_lemma.
             apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      Unshelve.
      rewrite <- assoc. rewrite BinProductPr2Commutes. apply id_right.
  Qed.

  Lemma DCM_rightunitor_law : disp_rightunitor_law DCM_rightunitor_data DCM_rightunitorinv_data.
  Proof.
    split; [| split]; try red; intros.
    - cbn. unfold DCM_rightunitor_data.
      etrans.
      { apply dispBinProductOfArrowsPr1. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - cbn. unfold DCM_rightunitorinv_data, DCM_rightunitor_data.
      rewrite dispBinProductPr1Commutes.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - cbn. unfold DCM_rightunitorinv_data, DCM_rightunitor_data.
      apply pathsinv0.
      etrans.
      2: { apply dispBinProduct_endo_is_identity.
           + rewrite assoc_disp_var.
             rewrite dispBinProductPr1Commutes.
             apply pathsinv0, transportf_comp_lemma.
             etrans.
             2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
             rewrite id_right_disp.
             rewrite transport_f_b.
             apply transportf_comp_lemma.
             apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
           + apply dispTerminalArrowEq.
      }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      Unshelve.
      rewrite <- assoc. rewrite BinProductPr1Commutes. apply id_right.
  Qed.

  Lemma DCM_associator_law : disp_associator_law DCM_associator_data DCM_associatorinv_data.
  Proof.
    repeat split; try red; intros.
    - unfold DCM_associator_data. cbn.
      rewrite dispPostcompWithBinProductArrow.
      apply pathsinv0, transportf_comp_lemma.
      apply dispBinProductArrowUnique.
      + rewrite id_right_disp.
        rewrite transport_b_b.
        etrans.
        { apply mor_disp_transportf_postwhisker. }
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        rewrite dispBinProductPr1Commutes.
        apply transportf_comp_lemma.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
        apply transportf_comp_lemma.
        rewrite assoc_disp.
        rewrite dispBinProductOfArrowsPr1.
        apply transportf_comp_lemma.
        rewrite id_right_disp.
        rewrite transport_b_b.
        etrans.
        2: { apply pathsinv0, mor_disp_transportf_postwhisker. }
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite assoc_disp_var.
        rewrite dispBinProductPr2Commutes.
        rewrite transport_f_f.
        etrans.
        { apply maponpaths.
          apply mor_disp_transportf_prewhisker. }
        rewrite transport_f_f.
        rewrite dispPrecompWithBinProductArrow.
        rewrite transport_f_b.
        apply pathsinv0, transportf_comp_lemma.
        apply dispBinProductArrowUnique.
        * etrans.
          { apply mor_disp_transportf_postwhisker. }
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp_var.
          rewrite dispBinProductOfArrowsPr1.
          rewrite id_right_disp.
          rewrite transport_b_b.
          apply transportf_comp_lemma.
          etrans.
          2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
          rewrite dispBinProductPr1Commutes.
          rewrite transport_f_b.
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp.
          rewrite dispBinProductOfArrowsPr1.
          rewrite id_right_disp.
          rewrite transport_b_b.
          etrans.
          2: { apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker. }
          rewrite transport_b_f.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        * etrans.
          { apply mor_disp_transportf_postwhisker. }
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp_var.
          rewrite dispBinProductOfArrowsPr2.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          rewrite dispBinProductOfArrowsPr2.
          etrans.
          2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
          apply transportf_comp_lemma.
          rewrite assoc_disp.
          rewrite dispBinProductPr2Commutes.
          etrans.
          2: { apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker. }
          rewrite transport_b_f.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - unfold DCM_associator_data. cbn.
      rewrite dispPostcompWithBinProductArrow.
      apply pathsinv0, transportf_comp_lemma.
      apply dispBinProductArrowUnique.
      + rewrite dispPrecompWithBinProductArrow.
        rewrite transport_f_b.
        etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite dispBinProductPr1Commutes.
        rewrite transport_f_b.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp.
        rewrite dispBinProductOfArrowsPr1.
        etrans.
        2: { apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker. }
        rewrite transport_b_f.
        etrans.
        2: { rewrite assoc_disp_var.
             rewrite dispBinProductOfArrowsPr1.
             rewrite transport_f_f.
             unfold transportb.
             rewrite mor_disp_transportf_prewhisker.
             rewrite transport_f_f.
             rewrite assoc_disp.
             rewrite transport_f_b.
             apply idpath.
        }
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite assoc_disp_var.
        rewrite dispBinProductPr2Commutes.
        rewrite transport_f_f.
        etrans.
        { apply maponpaths.
          apply mor_disp_transportf_prewhisker. }
        rewrite transport_f_f.
        rewrite dispPrecompWithBinProductArrow.
        rewrite transport_f_b.
        apply pathsinv0, transportf_comp_lemma.
        apply dispBinProductArrowUnique.
        * rewrite id_right_disp.
          rewrite transport_f_b.
          etrans.
          { apply mor_disp_transportf_postwhisker. }
          apply pathsinv0, transportf_comp_lemma.
          rewrite dispBinProductPr1Commutes.
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp.
          rewrite dispBinProductOfArrowsPr1.
          etrans.
          2: { apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker. }
          rewrite transport_b_f.
          apply transportf_comp_lemma.
          rewrite assoc_disp_var.
          rewrite dispBinProductOfArrowsPr2.
          rewrite id_right_disp.
          rewrite transport_b_b.
          etrans.
          2: { apply maponpaths, pathsinv0, mor_disp_transportf_prewhisker. }
          rewrite transport_f_f.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        * etrans.
          { apply mor_disp_transportf_postwhisker. }
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp_var.
          rewrite dispBinProductOfArrowsPr2.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          rewrite id_left_disp.
          etrans.
          2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
          rewrite id_right_disp.
          rewrite transport_f_b.
          rewrite dispBinProductPr2Commutes.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - unfold DCM_associator_data. cbn.
      rewrite dispPostcompWithBinProductArrow.
      apply pathsinv0, transportf_comp_lemma.
      apply dispBinProductArrowUnique.
      + rewrite dispPrecompWithBinProductArrow.
        rewrite transport_f_b.
        etrans.
        { apply mor_disp_transportf_postwhisker. }
        rewrite dispBinProductPr1Commutes.
        rewrite transport_f_b.
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp.
        rewrite dispBinProductOfArrowsPr1.
        etrans.
        2: { apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker. }
        rewrite transport_b_f.
        etrans.
        2: { rewrite assoc_disp_var.
             rewrite dispBinProductOfArrowsPr1.
             rewrite transport_f_f.
             unfold transportb.
             rewrite mor_disp_transportf_prewhisker.
             rewrite transport_f_f.
             rewrite id_right_disp.
             unfold transportb.
             rewrite mor_disp_transportf_prewhisker.
             rewrite transport_f_f.
             apply idpath.
        }
        apply pathsinv0, transportf_comp_lemma.
        rewrite assoc_disp_var.
        rewrite id_right_disp.
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      + etrans; [apply mor_disp_transportf_postwhisker |].
        rewrite assoc_disp_var.
        rewrite dispBinProductPr2Commutes.
        rewrite transport_f_f.
        etrans; [apply maponpaths, mor_disp_transportf_prewhisker |].
        rewrite transport_f_f.
        rewrite dispPrecompWithBinProductArrow.
        rewrite transport_f_b.
        apply pathsinv0, transportf_comp_lemma.
        apply dispBinProductArrowUnique.
        * etrans; [apply mor_disp_transportf_postwhisker |].
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp_var.
          rewrite dispBinProductOfArrowsPr1.
          etrans; [| apply maponpaths, pathsinv0, mor_disp_transportf_prewhisker].
          rewrite transport_f_f.
          apply transportf_comp_lemma.
          etrans.
          2: { rewrite assoc_disp.
               rewrite dispBinProductPr1Commutes.
               unfold transportb.
               rewrite mor_disp_transportf_postwhisker.
               rewrite transport_f_f.
               apply idpath.
          }
          apply pathsinv0, transportf_comp_lemma.
          etrans.
          2: { rewrite assoc_disp.
               rewrite dispBinProductOfArrowsPr1.
               apply maponpaths.
               apply pathsinv0, mor_disp_transportf_postwhisker. }
          rewrite transport_b_f.
          etrans.
          2: { rewrite assoc_disp_var.
               rewrite dispBinProductOfArrowsPr2.
               unfold transportb.
               rewrite mor_disp_transportf_prewhisker.
               rewrite transport_f_f.
               rewrite assoc_disp.
               rewrite transport_f_f.
               rewrite transport_f_b.
               apply idpath.
          }
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        * etrans; [apply mor_disp_transportf_postwhisker |].
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp_var.
          do 2 rewrite dispBinProductOfArrowsPr2.
          rewrite transport_f_b.
          rewrite id_right_disp.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          etrans; [| apply pathsinv0, mor_disp_transportf_prewhisker].
          rewrite id_right_disp.
          etrans; [| apply maponpaths, pathsinv0, mor_disp_transportf_prewhisker].
          rewrite dispBinProductPr2Commutes.
          rewrite transport_f_f.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - unfold DCM_associator_data, DCM_associatorinv_data. cbn.
      etrans. (* creates a shelved goal *)
      { apply pathsinv0, dispBinProduct_endo_is_identity. (* creates a shelved goal *)
        + rewrite assoc_disp_var.
          rewrite dispBinProductPr1Commutes.
          etrans; [apply maponpaths, mor_disp_transportf_prewhisker |].
          rewrite transport_f_f.
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp.
          rewrite dispBinProductPr1Commutes.
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite dispBinProductPr1Commutes.
          rewrite transport_f_f.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        + rewrite assoc_disp_var.
          rewrite dispBinProductPr2Commutes.
          etrans; [apply maponpaths, mor_disp_transportf_prewhisker |].
          rewrite transport_f_f.
          apply pathsinv0, transportf_comp_lemma.
          rewrite dispPrecompWithBinProductArrow.
          apply transportf_comp_lemma.
          apply dispBinProductArrowUnique.
          * etrans; [apply mor_disp_transportf_postwhisker |].
            apply transportf_comp_lemma.
            rewrite assoc_disp.
            rewrite dispBinProductPr1Commutes.
            etrans; [| apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker].
            rewrite dispBinProductPr2Commutes.
            rewrite transport_b_f.
            rewrite transport_f_b.
            apply transportf_comp_lemma.
            apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
          * etrans; [apply mor_disp_transportf_postwhisker |].
            apply transportf_comp_lemma.
            rewrite dispBinProductPr2Commutes.
            apply transportf_comp_lemma.
            apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      }
(* still two goals to unshelve! *)
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - unfold DCM_associator_data, DCM_associatorinv_data. cbn.
      etrans. (* creates a shelved goal *)
      { apply pathsinv0, dispBinProduct_endo_is_identity. (* creates a shelved goal *)
        + rewrite assoc_disp_var.
          rewrite dispBinProductPr1Commutes.
          apply pathsinv0, transportf_comp_lemma.
          etrans; [| apply pathsinv0, mor_disp_transportf_prewhisker].
          rewrite dispPrecompWithBinProductArrow.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          apply dispBinProductArrowUnique.
          * etrans; [apply mor_disp_transportf_postwhisker |].
            apply transportf_comp_lemma.
            rewrite dispBinProductPr1Commutes.
            apply transportf_comp_lemma.
            apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
          * etrans; [apply mor_disp_transportf_postwhisker |].
            apply transportf_comp_lemma.
            rewrite assoc_disp.
            rewrite dispBinProductPr2Commutes.
            etrans; [| apply maponpaths, pathsinv0, mor_disp_transportf_postwhisker].
            rewrite dispBinProductPr1Commutes.
            rewrite transport_b_f.
            rewrite transport_f_b.
            apply transportf_comp_lemma.
            apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        + rewrite assoc_disp_var.
          rewrite dispBinProductPr2Commutes.
          etrans; [apply maponpaths, mor_disp_transportf_prewhisker |].
          rewrite transport_f_f.
          apply pathsinv0, transportf_comp_lemma.
          rewrite assoc_disp.
          rewrite dispBinProductPr2Commutes.
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite dispBinProductPr2Commutes.
          rewrite transport_f_f.
          rewrite transport_f_b.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      }
(* still two more goals to unshelve! *)
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      Unshelve.
      + change (αinv^{M}_{ x, y, z} · α^{M}_{ x, y, z} · BinProductPr1 C (CP x (y ⊗_{M} z)) = BinProductPr1 C (CP x (y ⊗_{M} z))). (** it thus appears as intermediary result in Lemma [CartesianMonoidalCategoriesWhiskered.associator_law_from_binprod], but we reporve it here, analogously with the three other goals *)
        cbn.
        rewrite <- assoc.
        rewrite BinProductPr1Commutes.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        apply BinProductPr1Commutes.
      + change( αinv^{M}_{ x, y, z} · α^{M}_{ x, y, z} · BinProductPr2 C (CP x (y ⊗_{M} z)) = BinProductPr2 C (CP x (y ⊗_{M} z))).
        cbn.
        rewrite <- assoc.
        rewrite BinProductPr2Commutes.
        rewrite precompWithBinProductArrow.
        rewrite BinProductPr2Commutes.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        apply pathsinv0, BinProductArrowUnique; apply idpath.
      + change (α^{M}_{ x, y, z} · αinv^{M}_{ x, y, z} · BinProductPr1 C (CP (x ⊗_{M} y) z) = BinProductPr1 C (CP (x ⊗_{M} y) z)).
        cbn.
        rewrite <- assoc.
        rewrite BinProductPr1Commutes.
        rewrite precompWithBinProductArrow.
        apply pathsinv0, BinProductArrowUnique.
        * apply pathsinv0, BinProductPr1Commutes.
        * rewrite assoc.
          rewrite BinProductPr2Commutes.
          apply pathsinv0, BinProductPr1Commutes.
      + change (α^{M}_{ x, y, z} · αinv^{M}_{ x, y, z} · BinProductPr2 C (CP (x ⊗_{M} y) z) = BinProductPr2 C (CP (x ⊗_{M} y) z)).
        cbn.
        rewrite <- assoc.
        rewrite BinProductPr2Commutes.
        rewrite assoc.
        rewrite BinProductPr2Commutes.
        apply BinProductPr2Commutes.
  Qed.


  Lemma DCM_triangle_identity : disp_triangle_identity DCM_leftunitor_data DCM_rightunitor_data DCM_associator_data.
  Proof.
    red; intros.
    cbn. unfold DCM_associator_data.
    rewrite dispPostcompWithBinProductArrow.
    apply pathsinv0, transportf_comp_lemma.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, dispBinProductOfArrowsPr1. }
      unfold DCM_rightunitor_data.
      rewrite assoc_disp_var.
      rewrite id_right_disp.
      rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, dispBinProductOfArrowsPr2. }
      rewrite id_right_disp.
      unfold DCM_leftunitor_data.
      apply pathsinv0, transportf_comp_lemma.
      rewrite dispBinProductPr2Commutes.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
  Qed.

  Lemma DCM_pentagon_identity : disp_pentagon_identity DCM_associator_data.
  Proof.
    red; intros.
    unfold DCM_associator_data. cbn.
    etrans.
    { apply assoc_disp_var. }
    apply pathsinv0, transportf_comp_lemma.
    etrans.
    2: { rewrite dispPostcompWithBinProductArrow.
         rewrite dispPrecompWithBinProductArrow.
         unfold transportb.
         apply pathsinv0, mor_disp_transportf_prewhisker. }
    etrans.
    2: { apply maponpaths, pathsinv0, dispPrecompWithBinProductArrow. }
    rewrite transport_f_b.
    apply pathsinv0, transportf_comp_lemma.
    etrans.
    2: { apply pathsinv0, dispPrecompWithBinProductArrow. }
    apply transportf_comp_lemma.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { rewrite dispBinProductPr1Commutes.
           apply maponpaths.
           rewrite id_right_disp.
           unfold transportb.
           rewrite mor_disp_transportf_prewhisker.
           apply maponpaths.
           rewrite assoc_disp.
           apply maponpaths.
           rewrite dispBinProductOfArrowsPr1.
           unfold transportb.
           rewrite mor_disp_transportf_postwhisker.
           apply maponpaths.
           rewrite assoc_disp_var.
           rewrite dispBinProductPr1Commutes.
           unfold transportb.
           rewrite mor_disp_transportf_prewhisker.
           rewrite assoc_disp.
           rewrite transport_f_f.
           rewrite transport_f_b.
           apply idpath.
      }
      rewrite transport_b_f.
      rewrite transport_f_b.
      do 2 rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { rewrite assoc_disp.
           apply maponpaths.
           rewrite dispBinProductPr1Commutes.
           unfold transportb.
           rewrite mor_disp_transportf_postwhisker.
           apply idpath.
      }
      rewrite transport_b_f.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { rewrite dispBinProductPr2Commutes.
           apply maponpaths.
           rewrite mor_disp_transportf_prewhisker.
           apply maponpaths.
           apply pathsinv0, dispPrecompWithBinProductArrow. }
      rewrite transport_b_f.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      apply dispBinProductArrowUnique.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        apply pathsinv0, transportf_comp_lemma.
        etrans.
        2: { rewrite dispPrecompWithBinProductArrow.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             apply maponpaths.
             rewrite dispBinProductPr1Commutes.
             apply maponpaths.
             rewrite assoc_disp.
             apply maponpaths.
             rewrite dispBinProductPr1Commutes.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             apply idpath.
        }
        do 2 rewrite transport_f_b.
        rewrite transport_f_f.
        apply pathsinv0, transportf_comp_lemma.
        etrans.
        2: { apply maponpaths. rewrite assoc_disp.
             apply maponpaths.
             rewrite dispBinProductPr1Commutes.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             apply idpath. }
        etrans.
        2: { rewrite transport_b_f.
             rewrite mor_disp_transportf_prewhisker.
             apply maponpaths.
             rewrite assoc_disp.
             apply maponpaths.
             rewrite assoc_disp.
             rewrite dispBinProductOfArrowsPr1.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             rewrite assoc_disp_var.
             rewrite transport_f_f.
             apply maponpaths.
             rewrite mor_disp_transportf_postwhisker.
             apply maponpaths.
             rewrite assoc_disp_var.
             apply maponpaths.
             apply maponpaths.
             rewrite assoc_disp.
             rewrite dispBinProductPr2Commutes.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             rewrite dispBinProductPr1Commutes.
             rewrite transport_f_f.
             rewrite transport_f_b.
             apply idpath.
        }
        rewrite transport_f_b.
        rewrite mor_disp_transportf_prewhisker.
        do 4 rewrite transport_f_f.
        apply transportf_comp_lemma.
        rewrite assoc_disp.
        apply transportf_comp_lemma.
        apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
      + etrans.
        { apply mor_disp_transportf_postwhisker. }
        apply pathsinv0, transportf_comp_lemma.
        etrans.
        2: { rewrite dispPrecompWithBinProductArrow.
             unfold transportb.
             rewrite mor_disp_transportf_postwhisker.
             apply maponpaths.
             rewrite dispBinProductPr2Commutes.
             apply maponpaths.
             rewrite dispBinProductPr2Commutes.
             apply idpath.
        }
        do 2 rewrite transport_f_b.
        apply transportf_comp_lemma.
        apply dispBinProductArrowUnique.
        * rewrite mor_disp_transportf_postwhisker.
          apply pathsinv0, transportf_comp_lemma.
          etrans.
          2: { rewrite assoc_disp_var.
               apply maponpaths.
               apply maponpaths.
               rewrite assoc_disp_var.
               rewrite dispBinProductPr1Commutes.
               unfold transportb.
               rewrite mor_disp_transportf_prewhisker.
               rewrite transport_f_f.
               rewrite assoc_disp.
               rewrite dispBinProductPr1Commutes.
               unfold transportb.
               rewrite mor_disp_transportf_postwhisker.
               do 2 rewrite transport_f_f.
               apply idpath.
          }
          etrans.
          2: { rewrite mor_disp_transportf_prewhisker.
               rewrite transport_f_f.
               apply idpath. }
          apply transportf_comp_lemma.
          etrans.
          2: { apply maponpaths.
               rewrite assoc_disp_var.
               apply idpath. }
          etrans.
          2: { rewrite mor_disp_transportf_prewhisker.
               apply maponpaths.
               rewrite assoc_disp.
               rewrite dispBinProductOfArrowsPr1.
               unfold transportb.
               rewrite mor_disp_transportf_postwhisker.
               rewrite transport_f_f.
               apply maponpaths.
               rewrite assoc_disp_var.
               do 2 apply maponpaths.
               rewrite assoc_disp.
               rewrite dispBinProductPr2Commutes.
               unfold transportb.
               rewrite mor_disp_transportf_postwhisker.
               rewrite transport_f_f.
               rewrite dispBinProductPr2Commutes.
               rewrite transport_f_b.
               apply idpath.
          }
          rewrite mor_disp_transportf_prewhisker.
          do 3 rewrite transport_f_f.
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
        * rewrite mor_disp_transportf_postwhisker.
          apply pathsinv0, transportf_comp_lemma.
          etrans.
          2: { rewrite assoc_disp_var.
               apply maponpaths.
               apply maponpaths.
               rewrite assoc_disp_var.
               rewrite dispBinProductPr2Commutes.
               unfold transportb.
               rewrite mor_disp_transportf_prewhisker.
               rewrite transport_f_f.
               rewrite dispBinProductPr2Commutes.
               rewrite transport_f_b.
               apply idpath.
          }
          rewrite mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          apply transportf_comp_lemma.
          etrans.
          2: { rewrite dispBinProductOfArrowsPr2.
               rewrite id_right_disp.
               rewrite transport_b_b.
               apply idpath. }
          apply transportf_comp_lemma.
          apply transportf_comp_lemma_hset; try apply homset_property; apply idpath.
  Qed.

  Lemma DCM_laws : disp_monoidal_laws DCM_data.
  Proof.
    exists DCM_leftunitor_law.
    exists DCM_rightunitor_law.
    exists DCM_associator_law.
    exists DCM_triangle_identity.
    exact DCM_pentagon_identity.
  Qed.

  Definition displayedcartesianmonoidalcat: disp_monoidal D M := DCM_data ,, DCM_laws.


End FixADisplayedCategory.
