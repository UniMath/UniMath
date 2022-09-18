Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section GeneralConstruction.

Context (C : category)(CP : BinProducts C)(terminal : Terminal C).


Definition tensorfrombinprod_data: bifunctor_data C C C.
Proof.
  use make_bifunctor_data.
    + intros c1 c2. exact (BinProductObject _ (CP c1 c2)).
    + intros b c1 c2 g.
      apply BinProductOfArrows.
      * apply identity.
      * exact g.
    + intros b1 b2 c f.
      apply BinProductOfArrows.
      * exact f.
      * apply identity.
Defined.

Lemma is_bifunctor_tensorfrombinprod_data : is_bifunctor tensorfrombinprod_data.
Proof.
  repeat split; red; cbn.
    + intros b c.
      apply pathsinv0, BinProduct_endo_is_identity.
      * now rewrite BinProductOfArrowsPr1, id_right.
      * now rewrite BinProductOfArrowsPr2, id_right.
    + intros b c.
      apply pathsinv0, BinProduct_endo_is_identity.
      * now rewrite BinProductOfArrowsPr1, id_right.
      * now rewrite BinProductOfArrowsPr2, id_right.
    + intros b c1 c2 c3 g1 g2.
      now rewrite BinProductOfArrows_comp, id_right.
    + intros b1 b2 b3 c f1 f2.
      now rewrite BinProductOfArrows_comp, id_right.
    + intros b1 b2 c1 c2 f g.
      unfold functoronmorphisms1, functoronmorphisms2.
      unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms.
      cbn.
      do 2 rewrite BinProductOfArrows_comp.
      do 2 rewrite id_right.
      do 2 rewrite id_left.
      apply idpath.
Qed.

(** the following is merely a variant of [binproduct_functor] *)
Definition tensorfrombinprod: tensor C.
Proof.
  use make_bifunctor.
  - exact tensorfrombinprod_data.
  - exact is_bifunctor_tensorfrombinprod_data.
Defined.

Definition cartesianmonoidalcat_data : monoidal_data C.
Proof.
  use make_monoidal_data.
  - exact tensorfrombinprod.
  - exact (TerminalObject terminal).
  - intro c. apply BinProductPr2.
  - intro c. apply BinProductArrow.
      * apply TerminalArrow.
      * exact (identity c).
  - intro c. apply BinProductPr1.
  - intro c. apply BinProductArrow.
    * exact (identity c).
    * apply TerminalArrow.
  - intros c1 c2 c3.
    apply BinProductArrow.
    + use compose.
      2: {apply BinProductPr1. }
      apply BinProductPr1.
    + apply BinProductArrow.
      * use compose.
        2: {apply BinProductPr1. }
        apply BinProductPr2.
      * apply BinProductPr2.
  - intros a b c.
    apply BinProductArrow.
    + apply BinProductArrow.
      * apply BinProductPr1.
      * use compose.
        2: {apply BinProductPr2. }
        apply BinProductPr1.
    + use compose.
      2: {apply BinProductPr2. }
      apply BinProductPr2.
Defined.

Local Definition MD := cartesianmonoidalcat_data.

Local Lemma leftunitor_law_from_binprod: leftunitor_law lu_{MD} luinv_{MD}.
Proof.
  split.
  - intros c1 c2 f.
    cbn.
    apply BinProductOfArrowsPr2.
  - split.
    + apply pathsinv0, BinProduct_endo_is_identity.
      * (* show_id_type. *)
        apply TerminalArrowEq.
      * rewrite <- assoc.
        etrans.
        { apply maponpaths. apply BinProductPr2Commutes. }
        apply id_right.
    + apply BinProductPr2Commutes.
Qed.

Local Lemma rightunitor_law_from_binprod: rightunitor_law ru_{MD} ruinv_{MD}.
Proof.
  split.
  - intros c1 c2 f.
    cbn.
    apply BinProductOfArrowsPr1.
  - intro c.
    split.
    + apply pathsinv0, BinProduct_endo_is_identity.
      * rewrite <- assoc.
        etrans.
        { apply maponpaths. apply BinProductPr1Commutes. }
        apply id_right.
      * apply TerminalArrowEq.
    + apply BinProductPr1Commutes.
Qed.

Local Lemma associator_law_from_binprod: associator_law α_{MD} αinv_{MD}.
Proof.
  repeat split.
  - intros a b c1 c2 h.
    unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms.
    cbn.
    rewrite postcompWithBinProductArrow.
    etrans.
    2: { apply pathsinv0, precompWithBinProductArrow. }
    apply BinProductArrowUnique.
    + rewrite BinProductPr1Commutes.
      rewrite id_right.
      unfold BinProductOfArrows.
      rewrite id_right.
      rewrite assoc.
      rewrite BinProductPr1Commutes.
      apply idpath.
    + rewrite id_right.
      rewrite BinProductPr2Commutes.
      rewrite postcompWithBinProductArrow.
      etrans.
      2: { apply pathsinv0, precompWithBinProductArrow. }
      apply BinProductArrowUnique.
      * rewrite BinProductPr1Commutes.
        rewrite id_right.
        unfold BinProductOfArrows.
        rewrite id_right.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        apply idpath.
      * rewrite id_right.
        rewrite BinProductPr2Commutes.
        unfold BinProductOfArrows.
        rewrite id_right.
        rewrite BinProductPr2Commutes.
        apply idpath.
  - intros a1 a2 b c f.
    unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms.
    cbn.
    rewrite postcompWithBinProductArrow.
    etrans.
    2: { apply pathsinv0, precompWithBinProductArrow. }
    apply BinProductArrowUnique.
    + rewrite BinProductPr1Commutes.
      rewrite assoc.
      unfold BinProductOfArrows.
      rewrite BinProductPr1Commutes.
      rewrite id_right.
      etrans.
      2: { rewrite <- assoc.
           rewrite BinProductPr1Commutes.
           apply assoc'.
      }
      apply idpath.
    + rewrite BinProductPr2Commutes.
      rewrite id_right.
      etrans.
      2: { apply pathsinv0, precompWithBinProductArrow. }
      apply BinProductArrowUnique.
      * rewrite BinProductPr1Commutes.
        unfold BinProductOfArrows.
        do 2 rewrite id_right.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite <- assoc.
        rewrite BinProductPr2Commutes.
        apply idpath.
      * rewrite BinProductPr2Commutes.
        unfold BinProductOfArrows.
        rewrite BinProductPr2Commutes.
        rewrite id_right.
        apply idpath.
  - intros a b1 b2 c g.
    unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms.
    cbn.
    rewrite postcompWithBinProductArrow.
    etrans.
    2: { apply pathsinv0, precompWithBinProductArrow. }
    apply BinProductArrowUnique.
    + rewrite BinProductPr1Commutes.
      rewrite id_right.
      rewrite assoc.
      unfold BinProductOfArrows.
      rewrite BinProductPr1Commutes.
      rewrite <- assoc.
      rewrite BinProductPr1Commutes.
      rewrite id_right.
      apply idpath.
    + rewrite BinProductPr2Commutes.
      rewrite postcompWithBinProductArrow.
      etrans.
      2: { apply pathsinv0, precompWithBinProductArrow. }
      rewrite id_right.
      apply BinProductArrowUnique.
      * rewrite BinProductPr1Commutes.
        unfold BinProductOfArrows.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        etrans.
        2: { rewrite <- assoc.
             rewrite BinProductPr2Commutes.
             apply assoc'. }
        apply idpath.
      * rewrite BinProductPr2Commutes.
        unfold BinProductOfArrows.
        rewrite BinProductPr2Commutes.
        rewrite id_right.
        apply idpath.
  - apply pathsinv0, BinProduct_endo_is_identity.
    -- cbn.
       rewrite <- assoc.
       rewrite BinProductPr1Commutes.
       rewrite precompWithBinProductArrow.
       apply pathsinv0, BinProductArrowUnique.
       ++ apply pathsinv0, BinProductPr1Commutes.
       ++ rewrite assoc.
          rewrite BinProductPr2Commutes.
          apply pathsinv0, BinProductPr1Commutes.
    -- cbn.
       rewrite <- assoc.
       rewrite BinProductPr2Commutes.
       rewrite assoc.
       rewrite BinProductPr2Commutes.
       apply BinProductPr2Commutes.
  - apply pathsinv0, BinProduct_endo_is_identity.
    -- cbn.
       rewrite <- assoc.
       rewrite BinProductPr1Commutes.
       rewrite assoc.
       rewrite BinProductPr1Commutes.
       apply BinProductPr1Commutes.
    -- cbn.
       rewrite <- assoc.
       rewrite BinProductPr2Commutes.
       rewrite precompWithBinProductArrow.
       rewrite BinProductPr2Commutes.
       rewrite assoc.
       rewrite BinProductPr1Commutes.
       rewrite BinProductPr2Commutes.
       apply pathsinv0, BinProductArrowUnique; apply idpath.
Qed.


Local Lemma triangle_identity_from_binprod: triangle_identity lu_{MD} ru_{MD} α_{MD}.
Proof.
  intros b c.
  cbn.
  rewrite postcompWithBinProductArrow.
  apply pathsinv0, BinProductArrowUnique.
  - rewrite BinProductOfArrowsPr1.
    rewrite id_right.
    apply idpath.
  - rewrite BinProductOfArrowsPr2.
    rewrite BinProductPr2Commutes.
    apply id_right.
Qed.

Local Lemma pentagon_identity_from_binprod: pentagon_identity α_{MD}.
Proof.
  intros a b c d.
  cbn.
  etrans.
  { rewrite <- assoc.
    rewrite postcompWithBinProductArrow.
    rewrite precompWithBinProductArrow.
    apply idpath. }
  etrans.
  2: { rewrite precompWithBinProductArrow.
       apply idpath. }
  apply BinProductArrowsEq; [do 2 rewrite BinProductPr1Commutes | do 2 rewrite BinProductPr2Commutes].
  - rewrite id_right.
    rewrite assoc.
    rewrite BinProductOfArrowsPr1.
    rewrite assoc.
    rewrite BinProductPr1Commutes.
    rewrite <- assoc.
    rewrite BinProductPr1Commutes.
    apply assoc.
  - etrans.
    { rewrite precompWithBinProductArrow.
      unfold BinProductOfArrows.
      rewrite precompWithBinProductArrow.
      apply idpath. }
    etrans.
    2: { rewrite precompWithBinProductArrow.
         apply idpath. }
    apply BinProductArrowsEq; [do 2 rewrite BinProductPr1Commutes | do 2 rewrite BinProductPr2Commutes].
    + etrans.
      2: { rewrite assoc.
           rewrite BinProductPr1Commutes.
           apply idpath. }
      etrans.
      { apply maponpaths.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        apply idpath. }
      repeat rewrite assoc.
      rewrite BinProductPr1Commutes.
      repeat rewrite <- assoc.
      apply maponpaths.
      rewrite assoc.
      rewrite BinProductPr2Commutes.
      apply BinProductPr1Commutes.
    + rewrite BinProductPr2Commutes.
      do 4 rewrite precompWithBinProductArrow.
      apply BinProductArrowsEq; [do 2 rewrite BinProductPr1Commutes | do 2 rewrite BinProductPr2Commutes].
      * etrans.
        { apply maponpaths.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        apply idpath. }
        repeat rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        apply BinProductPr2Commutes.
      * do 2 rewrite BinProductPr2Commutes.
        apply id_right.
Qed.

Definition cartesianmonoidalcat: monoidal C.
Proof.
  exists cartesianmonoidalcat_data.
  exists leftunitor_law_from_binprod.
  exists rightunitor_law_from_binprod.
  exists associator_law_from_binprod.
  exists triangle_identity_from_binprod.
  exact pentagon_identity_from_binprod.
Defined.

End GeneralConstruction.


Definition SET_cartesian_monoidal : monoidal SET.
Proof.
  apply cartesianmonoidalcat.
  - apply BinProductsHSET.
  - apply TerminalHSET.
Defined.
