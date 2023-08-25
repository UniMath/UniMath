(********************************************************************

 Construction of cartesian monoidal categories

 Every category with binary products and a terminal object gives rise
 to a monoidal category.

 Contents
 1. Construction of cartesian monoidal categories
 2. Properties of cartesian monoidal categories
 3. Cartesian closed categories
 4. Set as cartesian monoidal category
 5. Useful lemmas

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/CartesianMonoidalCategoriesWhiskered.v

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

(**
 1. Construction of cartesian monoidal categories
 *)
Section GeneralConstruction.
  Context (C : category)
          (CP : BinProducts C)
          (terminal : Terminal C).

  Definition tensorfrombinprod_data: bifunctor_data C C C.
  Proof.
    use make_bifunctor_data.
    - intros c1 c2. exact (BinProductObject _ (CP c1 c2)).
    - intros b c1 c2 g.
      use BinProductOfArrows.
      + apply identity.
      + exact g.
    - intros b1 b2 c f.
      use BinProductOfArrows.
      + exact f.
      + apply identity.
  Defined.

  Lemma is_bifunctor_tensorfrombinprod_data : is_bifunctor tensorfrombinprod_data.
  Proof.
    repeat split; red; cbn.
    - intros b c.
      apply pathsinv0, BinProduct_endo_is_identity.
      + now rewrite BinProductOfArrowsPr1, id_right.
      + now rewrite BinProductOfArrowsPr2, id_right.
    - intros b c.
      apply pathsinv0, BinProduct_endo_is_identity.
      + now rewrite BinProductOfArrowsPr1, id_right.
      + now rewrite BinProductOfArrowsPr2, id_right.
    - intros b c1 c2 c3 g1 g2.
      now rewrite BinProductOfArrows_comp, id_right.
    - intros b1 b2 b3 c f1 f2.
      now rewrite BinProductOfArrows_comp, id_right.
    - intros b1 b2 c1 c2 f g.
      unfold functoronmorphisms1, functoronmorphisms2.
      unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms.
      cbn.
      do 2 rewrite BinProductOfArrows_comp.
      do 2 rewrite id_right.
      do 2 rewrite id_left.
      apply idpath.
  Qed.

  (** the following is merely a variant of [binproduct_functor] *)
  Definition tensorfrombinprod : bifunctor C C C.
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
    apply BinProductArrowsEq.
    - do 2 rewrite BinProductPr1Commutes.
      rewrite id_right.
      rewrite assoc.
      rewrite BinProductOfArrowsPr1.
      rewrite assoc.
      rewrite BinProductPr1Commutes.
      rewrite <- assoc.
      rewrite BinProductPr1Commutes.
      apply assoc.
    - do 2 rewrite BinProductPr2Commutes.
      etrans.
      { rewrite precompWithBinProductArrow.
        unfold BinProductOfArrows.
        rewrite precompWithBinProductArrow.
        apply idpath. }
      etrans.
      2: { rewrite precompWithBinProductArrow.
           apply idpath. }
      apply BinProductArrowsEq.
      + do 2 rewrite BinProductPr1Commutes.
        etrans.
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
      + do 2 rewrite BinProductPr2Commutes.
        rewrite BinProductPr2Commutes.
        do 4 rewrite precompWithBinProductArrow.
        apply BinProductArrowsEq.
        * do 2 rewrite BinProductPr1Commutes.
          etrans.
          { apply maponpaths.
            rewrite assoc.
            rewrite BinProductPr1Commutes.
            apply idpath. }
          repeat rewrite assoc.
          rewrite BinProductPr1Commutes.
          rewrite BinProductPr2Commutes.
          apply BinProductPr2Commutes.
        * do 4 rewrite BinProductPr2Commutes.
          apply id_right.
  Qed.

  Definition cartesian_monoidal : monoidal C.
  Proof.
    exists cartesianmonoidalcat_data.
    exists is_bifunctor_tensorfrombinprod_data.
    exists leftunitor_law_from_binprod.
    exists rightunitor_law_from_binprod.
    exists associator_law_from_binprod.
    exists triangle_identity_from_binprod.
    exact pentagon_identity_from_binprod.
  Defined.

  Definition cartesian_monoidalcat
    : monoidal_cat
    := C ,, cartesian_monoidal.

  (**
   2. Properties of cartesian monoidal categories
   *)
  Proposition is_semicartesian_cartesian_monoidalcat
    : is_semicartesian cartesian_monoidalcat.
  Proof.
    exact (pr2 terminal).
  Defined.

  Proposition is_cartesian_cartesian_monoidalcat
    : is_cartesian cartesian_monoidalcat.
  Proof.
    refine (is_semicartesian_cartesian_monoidalcat ,, _).
    intros x y ; cbn.
    use (isBinProduct_eq_arrow _ _ (pr2 (CP x y))).
    - abstract
        (unfold semi_cart_tensor_pr1 ; cbn ;
         unfold monoidal_cat_tensor_mor ;
         unfold functoronmorphisms1 ;
         cbn ;
         rewrite !assoc' ;
         rewrite BinProductOfArrowsPr1 ;
         rewrite id_right ;
         rewrite BinProductOfArrowsPr1 ;
         rewrite id_right ;
         apply idpath).
    - abstract
        (unfold semi_cart_tensor_pr2 ; cbn ;
         unfold monoidal_cat_tensor_mor ;
         unfold functoronmorphisms1 ;
         cbn ;
         rewrite !assoc' ;
         rewrite BinProductOfArrowsPr2 ;
         rewrite id_right ;
         rewrite BinProductOfArrowsPr2 ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition symmetric_cartesian_monoidalcat
    : symmetric cartesian_monoidalcat.
  Proof.
    use cartesian_to_symmetric.
    exact is_cartesian_cartesian_monoidalcat.
  Defined.

  (**
   3. Cartesian closed categories
   *)
  Definition sym_mon_closed_cartesian_cat
             (expC : Exponentials CP)
    : sym_mon_closed_cat.
  Proof.
    use make_sym_mon_closed_cat.
    - exact (cartesian_monoidalcat ,, symmetric_cartesian_monoidalcat).
    - exact (exp expC).
    - exact (exp_eval_alt expC).
    - exact (λ _ _ _ f, exp_lam_alt expC f).
    - abstract
        (cbn ;
         unfold monoidal_cat_tensor_mor ;
         unfold functoronmorphisms1 ;
         cbn ;
         intros x y z f ;
         refine (_ @ exp_beta_alt expC f) ;
         apply maponpaths_2 ;
         apply prod_lwhisker_rwhisker).
    - abstract
        (intros x y z f ; cbn in * ;
         unfold monoidal_cat_tensor_mor ;
         unfold functoronmorphisms1 ;
         cbn ;
         refine (exp_eta_alt expC f @ _) ;
         apply maponpaths ;
         apply maponpaths_2 ;
         refine (!_) ;
         apply prod_lwhisker_rwhisker).
  Defined.
End GeneralConstruction.

(**
 4. Set as cartesian monoidal category
 *)
Definition SET_cartesian_monoidal : monoidal SET.
Proof.
  apply cartesian_monoidal.
  - apply BinProductsHSET.
  - apply TerminalHSET.
Defined.

(**
 5. Useful lemmas
 *)
Proposition cartesian_semi_cart_tensor_pr1
            (VC : category)
            (TV : Terminal VC)
            (VP : BinProducts VC)
            (expV : Exponentials VP)
            (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
            (x y : V)
  : semi_cart_tensor_pr1
      (is_semicartesian_cartesian_monoidalcat VC VP TV)
      x
      y
    =
    BinProductPr1 _ _.
Proof.
  unfold semi_cart_tensor_pr1 ; cbn.
  unfold monoidal_cat_tensor_mor, functoronmorphisms1 ; cbn.
  rewrite !assoc'.
  rewrite BinProductOfArrowsPr1.
  rewrite id_right.
  rewrite BinProductOfArrowsPr1.
  apply id_right.
Qed.

Proposition cartesian_semi_cart_tensor_pr2
            (VC : category)
            (TV : Terminal VC)
            (VP : BinProducts VC)
            (expV : Exponentials VP)
            (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
            (x y : V)
  : semi_cart_tensor_pr2
      (is_semicartesian_cartesian_monoidalcat VC VP TV)
      x
      y
    =
    BinProductPr2 _ _.
Proof.
  unfold semi_cart_tensor_pr2 ; cbn.
  unfold monoidal_cat_tensor_mor, functoronmorphisms1 ; cbn.
  rewrite !assoc'.
  rewrite BinProductOfArrowsPr2.
  rewrite id_right.
  rewrite BinProductOfArrowsPr2.
  apply id_right.
Qed.

Proposition lassociator_hexagon_two
            (VC : category)
            (TV : Terminal VC)
            (VP : BinProducts VC)
            (expV : Exponentials VP)
            (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
            (x y z : V)
  : mon_lassociator x y z
    · sym_mon_braiding V x _
    · mon_lassociator y z x
    · sym_mon_braiding V y _
    · mon_lassociator z x y
    =
    sym_mon_braiding V _ z.
Proof.
  use BinProductArrowsEq ; cbn.
  - rewrite !assoc'.
    rewrite !BinProductPr1Commutes.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !assoc.
      rewrite BinProductPr1Commutes.
      apply idpath.
    }
    rewrite !cartesian_semi_cart_tensor_pr2.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply BinProductPr2Commutes.
    }
    rewrite BinProductPr1Commutes.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply BinProductPr1Commutes.
    }
    rewrite !assoc.
    rewrite !BinProductPr2Commutes.
    apply idpath.
  - rewrite !assoc'.
    rewrite !BinProductPr2Commutes.
    rewrite !cartesian_semi_cart_tensor_pr1, !cartesian_semi_cart_tensor_pr2.
    use BinProductArrowsEq.
    + rewrite !assoc'.
      rewrite !BinProductPr1Commutes.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite BinProductPr1Commutes.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite !BinProductPr2Commutes.
        apply idpath.
      }
      rewrite !BinProductPr2Commutes.
      rewrite !BinProductPr1Commutes.
      apply idpath.
    + rewrite !assoc'.
      rewrite !BinProductPr2Commutes.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite BinProductPr1Commutes.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite !BinProductPr1Commutes.
        apply idpath.
      }
      rewrite !assoc.
      rewrite !BinProductPr2Commutes.
      rewrite !BinProductPr1Commutes.
      apply idpath.
Qed.
