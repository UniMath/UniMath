(******************************************************************************

 Limits in the Eilenberg-Moore category

 Contents
 1. Terminal objects
 2. Binary products
 3. Pullbacks
 4. Initial objects
 5. Binary coproducts

 ******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.

Local Open Scope cat.

Section EilenbergMooreCategoryLimits.
  Context {C : category}
          (m : Monad C).

  (**
   1. Terminal objects
   *)
  Definition terminal_obj_eilenberg_moore_cat
             (T : C)
             (HT : isTerminal _ T)
    : eilenberg_moore_cat m.
  Proof.
    use make_ob_eilenberg_moore.
    - exact T.
    - apply (TerminalArrow (_ ,, HT)).
    - apply (@TerminalArrowEq _ (_ ,, HT)).
    - apply (@TerminalArrowEq _ (_ ,, HT)).
  Defined.

  Definition is_terminal_obj_eilenberg_moore_cat
             (T : eilenberg_moore_cat m)
             (HT : isTerminal _ (pr11 T))
    : isTerminal
        (eilenberg_moore_cat m)
        T.
  Proof.
    intro x.
    use make_iscontr.
    - use make_mor_eilenberg_moore.
      + apply (TerminalArrow (_ ,, HT)).
      + apply (@TerminalArrowEq _ (_ ,, HT)).
    - abstract
        (intro f ;
         use eq_mor_eilenberg_moore ;
         apply (@TerminalArrowEq _ (_ ,, HT))).
  Defined.

  Section Terminal.
    Context (T : Terminal C).

    Definition terminal_eilenberg_moore_cat
      : Terminal (eilenberg_moore_cat m).
    Proof.
      use make_Terminal.
      - exact (terminal_obj_eilenberg_moore_cat (pr1 T) (pr2 T)).
      - refine (is_terminal_obj_eilenberg_moore_cat _ _).
        exact (pr2 T).
    Defined.

    Definition eilenberg_moore_pr_preserves_terminal
      : preserves_terminal (eilenberg_moore_pr m).
    Proof.
      use preserves_terminal_if_preserves_chosen.
      - exact terminal_eilenberg_moore_cat.
      - unfold preserves_chosen_terminal.
        apply T.
    Defined.

    Definition functor_to_eilenberg_moore_cat_preserves_terminal
               {C' : category}
               (F : C' ⟶ C)
               (HF : preserves_terminal F)
               (α : F ∙ m ⟹ functor_identity C' ∙ F)
               (p₁ : ∏ (x : C'), η m (F x) · α x = identity (functor_identity C (F x)))
               (p₂ : ∏ (x : C'), # m (α x) · α x = μ m (F x) · α x)
      : preserves_terminal (functor_to_eilenberg_moore_cat m F α p₁ p₂).
    Proof.
      intros x Hx.
      use is_terminal_obj_eilenberg_moore_cat.
      apply HF.
      exact Hx.
    Defined.
  End Terminal.

  (**
   2. Binary products
   *)
  Section IsBinaryProduct.
    Context {x y p : eilenberg_moore_cat m}
            (π₁ : p --> x)
            (π₂ : p --> y)
            (H : isBinProduct C _ _ _ (pr11 π₁) (pr11 π₂)).

    Let P : BinProduct C (pr11 x) (pr11 y) := make_BinProduct _ _ _ _ _ _ H.

    Definition isBinProduct_eilenberg_moore_cat_unique
               {w : eilenberg_moore_cat m}
               (f : w --> x)
               (g : w --> y)
      : isaprop (∑ (k : w --> p), k · π₁ = f × k · π₂ = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_mor_eilenberg_moore.
      use (BinProductArrowsEq _ _ _ P).
      - exact (maponpaths (λ z, pr11 z) (pr12 φ₁) @ !(maponpaths (λ z, pr11 z) (pr12 φ₂))).
      - exact (maponpaths (λ z, pr11 z) (pr22 φ₁) @ !(maponpaths (λ z, pr11 z) (pr22 φ₂))).
    Qed.

    Definition isBinProduct_eilenberg_moore_cat_mor
               {w : eilenberg_moore_cat m}
               (f : w --> x)
               (g : w --> y)
      : w --> p.
    Proof.
      use make_mor_eilenberg_moore.
      - exact (BinProductArrow _ P (pr11 f) (pr11 g)).
      - use (BinProductArrowsEq _ _ _ P).
        + abstract
            (rewrite !assoc' ;
             etrans ;
             [ apply maponpaths ;
               apply (BinProductPr1Commutes _ _ _ P)
             | ] ;
             refine (eq_of_eilenberg_moore_mor f @ !_) ;
             etrans ;
             [ apply maponpaths ;
               exact (pr21 π₁)
             | ] ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             rewrite <- functor_comp ;
             apply maponpaths ;
             apply (BinProductPr1Commutes _ _ _ P)).
        + abstract
            (rewrite !assoc' ;
             etrans ;
             [ apply maponpaths ;
               apply (BinProductPr2Commutes _ _ _ P)
             | ] ;
             refine (eq_of_eilenberg_moore_mor g @ !_) ;
             etrans ;
             [ apply maponpaths ;
               exact (pr21 π₂)
             | ] ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             rewrite <- functor_comp ;
             apply maponpaths ;
             apply (BinProductPr2Commutes _ _ _ P)).
    Defined.

    Definition isBinProduct_eilenberg_moore_cat_pr1
               {w : eilenberg_moore_cat m}
               (f : w --> x)
               (g : w --> y)
      : isBinProduct_eilenberg_moore_cat_mor f g · π₁ = f.
    Proof.
      use eq_mor_eilenberg_moore.
      apply (BinProductPr1Commutes _ _ _ P).
    Qed.

    Definition isBinProduct_eilenberg_moore_cat_pr2
               {w : eilenberg_moore_cat m}
               (f : w --> x)
               (g : w --> y)
      : isBinProduct_eilenberg_moore_cat_mor f g · π₂ = g.
    Proof.
      use eq_mor_eilenberg_moore.
      apply (BinProductPr2Commutes _ _ _ P).
    Qed.

    Definition isBinProduct_eilenberg_moore_cat
      : isBinProduct _ x y p π₁ π₂.
    Proof.
      use make_isBinProduct.
      intros w f g.
      use iscontraprop1.
      - exact (isBinProduct_eilenberg_moore_cat_unique f g).
      - simple refine (_ ,, _ ,, _).
        + exact (isBinProduct_eilenberg_moore_cat_mor f g).
        + exact (isBinProduct_eilenberg_moore_cat_pr1 f g).
        + exact (isBinProduct_eilenberg_moore_cat_pr2 f g).
    Defined.
  End IsBinaryProduct.

  Section BinaryProducts.
    Context (P : BinProducts C).

    Definition BinProduct_obj_eilenberg_moore_cat_ob
               (x y : eilenberg_moore_cat m)
      : C
      := pr11 (P (pr11 x) (pr11 y)).

    Definition BinProduct_obj_eilenberg_moore_cat_mor
               (x y : eilenberg_moore_cat m)
      : m (BinProduct_obj_eilenberg_moore_cat_ob x y)
        -->
        BinProduct_obj_eilenberg_moore_cat_ob x y.
    Proof.
      use BinProductArrow.
      - exact (# m (BinProductPr1 _ _) · pr21 x).
      - exact (# m (BinProductPr2 _ _) · pr21 y).
    Defined.

    Definition BinProduct_obj_eilenberg_moore_cat_unit
               (x y : eilenberg_moore_cat m)
      : η m (BinProduct_obj_eilenberg_moore_cat_ob x y)
        · BinProduct_obj_eilenberg_moore_cat_mor x y
        =
        identity _.
    Proof.
      use BinProductArrowsEq.
      - rewrite !assoc', id_left.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (η m)).
        }
        cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact (pr12 x).
        }
        apply id_right.
      - rewrite !assoc', id_left.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr2Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (η m)).
        }
        cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact (pr12 y).
        }
        apply id_right.
    Qed.

    Definition BinProduct_obj_eilenberg_moore_cat_mult
               (x y : eilenberg_moore_cat m)
      : μ m (BinProduct_obj_eilenberg_moore_cat_ob x y)
        · BinProduct_obj_eilenberg_moore_cat_mor x y
        =
        # m (BinProduct_obj_eilenberg_moore_cat_mor x y)
        · BinProduct_obj_eilenberg_moore_cat_mor x y.
    Proof.
      use BinProductArrowsEq.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (μ m)).
        }
        cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (pr22 x).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply BinProductPr1Commutes.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr2Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (μ m)).
        }
        cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (pr22 y).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply BinProductPr2Commutes.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply BinProductPr2Commutes.
    Qed.

    Definition BinProduct_obj_eilenberg_moore_cat
               (x y : eilenberg_moore_cat m)
      : eilenberg_moore_cat m.
    Proof.
      use make_ob_eilenberg_moore.
      - exact (BinProduct_obj_eilenberg_moore_cat_ob x y).
      - exact (BinProduct_obj_eilenberg_moore_cat_mor x y).
      - exact (BinProduct_obj_eilenberg_moore_cat_unit x y).
      - exact (BinProduct_obj_eilenberg_moore_cat_mult x y).
    Defined.

    Definition BinProduct_pr1_eilenberg_moore_cat
               (x y : eilenberg_moore_cat m)
      : BinProduct_obj_eilenberg_moore_cat x y --> x.
    Proof.
      use make_mor_eilenberg_moore.
      - apply BinProductPr1.
      - apply BinProductPr1Commutes.
    Defined.

    Definition BinProduct_pr2_eilenberg_moore_cat
               (x y : eilenberg_moore_cat m)
      : BinProduct_obj_eilenberg_moore_cat x y --> y.
    Proof.
      use make_mor_eilenberg_moore.
      - apply BinProductPr2.
      - apply BinProductPr2Commutes.
    Defined.

    Definition BinProducts_eilenberg_moore_cat
      : BinProducts (eilenberg_moore_cat m).
    Proof.
      intros x y.
      use make_BinProduct.
      - exact (BinProduct_obj_eilenberg_moore_cat x y).
      - exact (BinProduct_pr1_eilenberg_moore_cat x y).
      - exact (BinProduct_pr2_eilenberg_moore_cat x y).
      - apply isBinProduct_eilenberg_moore_cat.
        apply P.
    Defined.

    Definition eilenberg_moore_pr_preserves_binproduct
      : preserves_binproduct (eilenberg_moore_pr m).
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      - exact BinProducts_eilenberg_moore_cat.
      - intros x y.
        apply P.
    Defined.

    Definition functor_to_eilenberg_moore_cat_preserves_binproduct
               {C' : category}
               (F : C' ⟶ C)
               (HF : preserves_binproduct F)
               (α : F ∙ m ⟹ functor_identity C' ∙ F)
               (p₁ : ∏ (x : C'), η m (F x) · α x = identity (functor_identity C (F x)))
               (p₂ : ∏ (x : C'), # m (α x) · α x = μ m (F x) · α x)
      : preserves_binproduct (functor_to_eilenberg_moore_cat m F α p₁ p₂).
    Proof.
      intros x y p π₁ π₂ Hx.
      use isBinProduct_eilenberg_moore_cat.
      apply HF.
      exact Hx.
    Defined.
  End BinaryProducts.

  (**
   3. Pullbacks
   *)
  Section IsPullback.
    Context {x y z : eilenberg_moore_cat m}
            {f : x --> z}
            {g : y --> z}
            {pb : eilenberg_moore_cat m}
            {π₁ : pb --> x}
            {π₂ : pb --> y}
            (q : π₁ · f = π₂ · g)
            (q' : pr11 π₁ · pr11 f = pr11 π₂ · pr11 g)
            (H : @isPullback
                   C
                   (pr11 z) (pr11 x) (pr11 y)
                   (pr11 pb)
                   (pr11 f) (pr11 g)
                   (pr11 π₁) (pr11 π₂)
                   q').

    Section UMP.
      Context {w : eilenberg_moore_cat m}
              (h : w --> x)
              (k : w --> y)
              (r : h · f = k · g).

      Definition isPullback_eilenberg_moore_unique
        : isaprop (∑ (hk : w --> pb), hk · π₁ = h × hk · π₂ = k).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use eq_mor_eilenberg_moore.
        use (MorphismsIntoPullbackEqual H).
        - exact (maponpaths (λ z, pr11 z) (pr12 φ₁ @ !(pr12 φ₂))).
        - exact (maponpaths (λ z, pr11 z) (pr22 φ₁ @ !(pr22 φ₂))).
      Qed.

      Definition isPullback_eilenberg_moore_mor
        : w --> pb.
      Proof.
        use make_mor_eilenberg_moore.
        - use (PullbackArrow (make_Pullback _ H)).
          + exact (mor_of_eilenberg_moore_mor h).
          + exact (mor_of_eilenberg_moore_mor k).
          + exact (maponpaths (λ z, pr11 z) r).
        - use (MorphismsIntoPullbackEqual H).
          + abstract
              (rewrite !assoc' ;
               etrans ;
                 [ apply maponpaths ;
                   apply (PullbackArrow_PullbackPr1 (make_Pullback _ H))
                 | ] ;
               refine (!_) ;
               etrans ;
                 [ apply maponpaths ;
                   exact (pr21 π₁)
                 | ] ;
               rewrite !assoc ;
               rewrite <- functor_comp ;
               etrans ;
                 [ apply maponpaths_2 ;
                   apply maponpaths ;
                   apply (PullbackArrow_PullbackPr1 (make_Pullback _ H))
                 | ] ;
               exact (!(eq_of_eilenberg_moore_mor h))).
          + abstract
              (rewrite !assoc' ;
               etrans ;
                 [ apply maponpaths ;
                   apply (PullbackArrow_PullbackPr2 (make_Pullback _ H))
                 | ] ;
               refine (!_) ;
               etrans ;
                 [ apply maponpaths ;
                   exact (pr21 π₂)
                 | ] ;
               rewrite !assoc ;
               rewrite <- functor_comp ;
               etrans ;
                 [ apply maponpaths_2 ;
                   apply maponpaths ;
                   apply (PullbackArrow_PullbackPr2 (make_Pullback _ H))
                 | ] ;
               exact (!(eq_of_eilenberg_moore_mor k))).
      Defined.
    End UMP.

    Definition isPullback_eilenberg_moore
      : isPullback q.
    Proof.
      intros w h k r.
      use iscontraprop1.
      - exact (isPullback_eilenberg_moore_unique h k).
      - simple refine (_ ,, _ ,, _).
        + exact (isPullback_eilenberg_moore_mor h k r).
        + abstract
            (use eq_mor_eilenberg_moore ;
             apply (PullbackArrow_PullbackPr1 (make_Pullback _ H))).
        + abstract
            (use eq_mor_eilenberg_moore ;
             apply (PullbackArrow_PullbackPr2 (make_Pullback _ H))).
    Defined.
  End IsPullback.

  Section Pullbacks.
    Context (PB : Pullbacks C).

    Section PullbackCone.
      Context {x y z : eilenberg_moore_cat m}
              (f : x --> z)
              (g : y --> z).

      Definition ob_of_pullbacks_eilenberg_moore_ob
        : C
        := PB _ _ _ (pr11 f) (pr11 g).

      Definition mor_of_pullbacks_eilenberg_moore_ob
        : m ob_of_pullbacks_eilenberg_moore_ob
          -->
          ob_of_pullbacks_eilenberg_moore_ob.
      Proof.
        use PullbackArrow.
        - exact (# m (PullbackPr1 (PB _ _ _ (pr11 f) (pr11 g))) · pr21 x).
        - exact (# m (PullbackPr2 (PB _ _ _ (pr11 f) (pr11 g))) · pr21 y).
        - abstract
            (rewrite !assoc' ;
             refine (maponpaths (λ z, _ · z) (pr21 f) @ _) ;
             refine (_ @ !(maponpaths (λ z, _ · z) (pr21 g))) ;
             rewrite !assoc ;
             rewrite <- !functor_comp ;
             apply maponpaths_2 ;
             apply maponpaths ;
             apply PullbackSqrCommutes).
      Defined.

      Definition pullbacks_eilenberg_moore_ob_unit
        : η m ob_of_pullbacks_eilenberg_moore_ob
          · mor_of_pullbacks_eilenberg_moore_ob
          =
          identity _.
      Proof.
        use (MorphismsIntoPullbackEqual (pr22 (PB _ _ _ (pr11 f) (pr11 g)))) ;
          unfold mor_of_pullbacks_eilenberg_moore_ob.
        - rewrite !assoc', id_left.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (nat_trans_ax (η m)).
          }
          cbn.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (pr12 x).
          }
          apply id_right.
        - rewrite !assoc', id_left.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (nat_trans_ax (η m)).
          }
          cbn.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (pr12 y).
          }
          apply id_right.
      Qed.

      Definition pullbacks_eilenberg_moore_ob_mult
        : μ m ob_of_pullbacks_eilenberg_moore_ob
          · mor_of_pullbacks_eilenberg_moore_ob
          =
          # m mor_of_pullbacks_eilenberg_moore_ob
          · mor_of_pullbacks_eilenberg_moore_ob.
      Proof.
        use (MorphismsIntoPullbackEqual (pr22 (PB _ _ _ (pr11 f) (pr11 g)))) ;
          unfold mor_of_pullbacks_eilenberg_moore_ob.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (nat_trans_ax (μ m)).
          }
          cbn.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (pr22 x).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          refine (!_).
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- functor_comp.
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (nat_trans_ax (μ m)).
          }
          cbn.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (pr22 y).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          refine (!_).
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- functor_comp.
          apply maponpaths.
          apply PullbackArrow_PullbackPr2.
      Qed.

      Definition pullbacks_eilenberg_moore_ob
        : eilenberg_moore_cat m.
      Proof.
        use make_ob_eilenberg_moore.
        - exact ob_of_pullbacks_eilenberg_moore_ob.
        - exact mor_of_pullbacks_eilenberg_moore_ob.
        - exact pullbacks_eilenberg_moore_ob_unit.
        - exact pullbacks_eilenberg_moore_ob_mult.
      Defined.

      Definition pullbacks_eilenberg_moore_pr1
        : pullbacks_eilenberg_moore_ob --> x.
      Proof.
        use make_mor_eilenberg_moore.
        - apply PullbackPr1.
        - apply PullbackArrow_PullbackPr1.
      Defined.

      Definition pullbacks_eilenberg_moore_pr2
        : pullbacks_eilenberg_moore_ob --> y.
      Proof.
        use make_mor_eilenberg_moore.
        - apply PullbackPr2.
        - apply PullbackArrow_PullbackPr2.
      Defined.

      Definition pullbacks_eilenberg_moore_eq
        : pullbacks_eilenberg_moore_pr1 · f
          =
          pullbacks_eilenberg_moore_pr2 · g.
      Proof.
        use eq_mor_eilenberg_moore.
        apply PullbackSqrCommutes.
      Qed.
    End PullbackCone.

    Definition Pullbacks_eilenberg_moore
      : Pullbacks (eilenberg_moore_cat m).
    Proof.
      intros x y z f g.
      use make_Pullback.
      - exact (pullbacks_eilenberg_moore_ob f g).
      - exact (pullbacks_eilenberg_moore_pr1 f g).
      - exact (pullbacks_eilenberg_moore_pr2 f g).
      - exact (pullbacks_eilenberg_moore_eq f g).
      - refine (isPullback_eilenberg_moore _ _ _).
        exact (pr22 (PB _ _ _ (pr11 f) (pr11 g))).
    Defined.

    Definition eilenberg_moore_pr_preserves_pullback
      : preserves_pullback (eilenberg_moore_pr m).
    Proof.
      use preserves_pullback_if_preserves_chosen.
      - exact Pullbacks_eilenberg_moore.
      - intro ; intros.
        apply PB.
    Defined.

    Definition functor_to_eilenberg_moore_cat_preserves_pullback
               {C' : category}
               (F : C' ⟶ C)
               (HF : preserves_pullback F)
               (α : F ∙ m ⟹ functor_identity C' ∙ F)
               (p₁ : ∏ (x : C'), η m (F x) · α x = identity (functor_identity C (F x)))
               (p₂ : ∏ (x : C'), # m (α x) · α x = μ m (F x) · α x)
      : preserves_pullback (functor_to_eilenberg_moore_cat m F α p₁ p₂).
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? Hx.
      use isPullback_eilenberg_moore.
      - abstract
          (cbn ;
           rewrite <- !functor_comp ;
           apply maponpaths ;
           exact q).
      - use HF.
        + exact q.
        + exact Hx.
    Defined.
  End Pullbacks.

  (**
   4. Initial objects
   *)
  Definition is_initial_eilenberg_moore_cat
             (I : eilenberg_moore_cat m)
             (HI : isInitial _ (pr11 I))
             (Hm : preserves_initial m)
    : isInitial (eilenberg_moore_cat m) I.
  Proof.
    use make_isInitial.
    intro x.
    use make_iscontr.
    - use make_mor_eilenberg_moore.
      + apply (InitialArrow (make_Initial _ HI)).
      + apply (@InitialArrowEq _ (make_Initial _ (Hm _ HI))).
    - abstract
        (intro f ;
         use eq_mor_eilenberg_moore ;
         apply (@InitialArrowEq _ (make_Initial _ HI))).
  Defined.

  Section Initial.
    Context (I : Initial C)
            (Hm : preserves_initial m).

    Definition initial_obj_eilenberg_moore_cat
      : eilenberg_moore_cat m.
    Proof.
      use make_ob_eilenberg_moore.
      - exact I.
      - apply (InitialArrow (make_Initial _ (Hm I (pr2 I)))).
      - apply InitialArrowEq.
      - apply (@InitialArrowEq _ (make_Initial _ (Hm _ (Hm I (pr2 I))))).
    Defined.

    Definition initial_eilenberg_moore_cat
      : Initial (eilenberg_moore_cat m).
    Proof.
      use make_Initial.
      - exact initial_obj_eilenberg_moore_cat.
      - apply is_initial_eilenberg_moore_cat.
        + exact (pr2 I).
        + exact Hm.
    Defined.

    Definition eilenberg_moore_pr_preserves_initial
      : preserves_initial (eilenberg_moore_pr m).
    Proof.
      use preserves_initial_if_preserves_chosen.
      - exact initial_eilenberg_moore_cat.
      - apply I.
    Defined.

    Definition functor_to_eilenberg_moore_cat_preserves_initial
               {C' : category}
               (F : C' ⟶ C)
               (HF : preserves_initial F)
               (α : F ∙ m ⟹ functor_identity C' ∙ F)
               (p₁ : ∏ (x : C'), η m (F x) · α x = identity (functor_identity C (F x)))
               (p₂ : ∏ (x : C'), # m (α x) · α x = μ m (F x) · α x)
      : preserves_initial (functor_to_eilenberg_moore_cat m F α p₁ p₂).
    Proof.
      intros x Hx.
      use is_initial_eilenberg_moore_cat.
      - apply HF.
        exact Hx.
      - exact Hm.
    Defined.
  End Initial.

  (**
   5. Binary coproducts
   *)
  Section IsBinaryCoproduct.
    Context (Hm : preserves_bincoproduct m)
            {x y sum : eilenberg_moore_cat m}
            (ι₁ : x --> sum)
            (ι₂ : y --> sum)
            (H : isBinCoproduct _ _ _ _ (pr11 ι₁) (pr11 ι₂)).

    Let copr : BinCoproduct (pr11 x) (pr11 y)
      := make_BinCoproduct _ _ _ _ _ _ H.

    Section UMP.
      Context {w : eilenberg_moore_cat m}
              (f : x --> w)
              (g : y --> w).

      Definition isBinCoproduct_eilenberg_moore_unique
        : isaprop (∑ (fg : sum --> w), ι₁ · fg = f × ι₂ · fg = g).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use eq_mor_eilenberg_moore.
        use (BinCoproductArrowsEq _ _ _ copr).
        - exact (maponpaths (λ z, pr11 z) (pr12 φ₁ @ !(pr12 φ₂))).
        - exact (maponpaths (λ z, pr11 z) (pr22 φ₁ @ !(pr22 φ₂))).
      Qed.

      Definition isBinCoproduct_eilenberg_moore_mor
        : sum --> w.
      Proof.
        use make_mor_eilenberg_moore.
        - exact (BinCoproductArrow copr (pr11 f) (pr11 g)).
        - use (BinCoproductArrowsEq
                 _ _ _
                 (make_BinCoproduct _ _ _ _ _ _ (Hm _ _ _ _ _ H))) ; cbn.
          + abstract
              (rewrite !assoc ;
               rewrite <- functor_comp ;
               etrans ;
               [ apply maponpaths_2 ;
                 exact (!(eq_of_eilenberg_moore_mor ι₁))
               | ] ;
               rewrite !assoc' ;
               etrans ;
               [ apply maponpaths ;
                 apply (BinCoproductIn1Commutes _ _ _ copr)
               | ] ;
               refine (!_) ;
               etrans ;
               [ apply maponpaths_2 ;
                 apply maponpaths ;
                 apply (BinCoproductIn1Commutes _ _ _ copr)
               | ] ;
               exact (!(eq_of_eilenberg_moore_mor f))).
          + abstract
              (rewrite !assoc ;
               rewrite <- functor_comp ;
               etrans ;
               [ apply maponpaths_2 ;
                 exact (!(eq_of_eilenberg_moore_mor ι₂))
               | ] ;
               rewrite !assoc' ;
               etrans ;
               [ apply maponpaths ;
                 apply (BinCoproductIn2Commutes _ _ _ copr)
               | ] ;
               refine (!_) ;
               etrans ;
               [ apply maponpaths_2 ;
                 apply maponpaths ;
                 apply (BinCoproductIn2Commutes _ _ _ copr)
               | ] ;
               exact (!(eq_of_eilenberg_moore_mor g))).
      Defined.

      Definition isBinCoproduct_eilenberg_moore_in1
        : ι₁ · isBinCoproduct_eilenberg_moore_mor = f.
      Proof.
        use eq_mor_eilenberg_moore.
        apply (BinCoproductIn1Commutes _ _ _ copr).
      Qed.

      Definition isBinCoproduct_eilenberg_moore_in2
        : ι₂ · isBinCoproduct_eilenberg_moore_mor = g.
      Proof.
        use eq_mor_eilenberg_moore.
        apply (BinCoproductIn2Commutes _ _ _ copr).
      Qed.
    End UMP.

    Definition isBinCoproduct_eilenberg_moore
      : isBinCoproduct _ _ _ _ ι₁ ι₂.
    Proof.
      intros w f g.
      use iscontraprop1.
      - exact (isBinCoproduct_eilenberg_moore_unique f g).
      - simple refine (_ ,, _ ,, _).
        + exact (isBinCoproduct_eilenberg_moore_mor f g).
        + exact (isBinCoproduct_eilenberg_moore_in1 f g).
        + exact (isBinCoproduct_eilenberg_moore_in2 f g).
    Defined.
  End IsBinaryCoproduct.

  Section BinaryCoproducts.
    Context (P : BinCoproducts C)
            (Hm : preserves_bincoproduct m).

    Definition bincoproduct_obj_eilenberg_moore_ob
               (x y : eilenberg_moore_cat m)
      : C
      := pr11 (P (pr11 x) (pr11 y)).

    Definition bincoproduct_obj_eilenberg_moore_ob_mor
               (x y : eilenberg_moore_cat m)
      : m (bincoproduct_obj_eilenberg_moore_ob x y)
        -->
        bincoproduct_obj_eilenberg_moore_ob x y.
    Proof.
      use (BinCoproductArrow
             (make_BinCoproduct
                _ _ _ _ _ _
                (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
      - exact (pr21 x · BinCoproductIn1 _).
      - exact (pr21 y · BinCoproductIn2 _).
    Defined.

    Definition bincoproduct_obj_eilenberg_moore_ob_unit
               (x y : eilenberg_moore_cat m)
      : η m (bincoproduct_obj_eilenberg_moore_ob x y)
        · bincoproduct_obj_eilenberg_moore_ob_mor x y
        =
        identity _.
    Proof.
      use BinCoproductArrowsEq ; unfold bincoproduct_obj_eilenberg_moore_ob_mor.
      - rewrite id_right.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax (η m)).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 x).
        }
        apply id_left.
      - rewrite id_right.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax (η m)).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 y).
        }
        apply id_left.
    Qed.

    Definition bincoproduct_obj_eilenberg_moore_ob_mult
               (x y : eilenberg_moore_cat m)
      : μ m (bincoproduct_obj_eilenberg_moore_ob x y)
        · bincoproduct_obj_eilenberg_moore_ob_mor x y
        =
        # m (bincoproduct_obj_eilenberg_moore_ob_mor x y)
        · bincoproduct_obj_eilenberg_moore_ob_mor x y.
    Proof.
      use (BinCoproductArrowsEq
             _ _ _
             (make_BinCoproduct
                _ _ _ _ _ _
                (Hm _ _ _ _ _ (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y))))))) ;
        unfold bincoproduct_obj_eilenberg_moore_ob_mor ; cbn.
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax (μ m)).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr22 x).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          rewrite <- functor_comp.
          apply maponpaths.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite functor_comp.
        rewrite !assoc'.
        apply maponpaths.
        apply (BinCoproductIn1Commutes
                 _ _ _
                 (make_BinCoproduct
                    _ _ _ _ _ _
                    (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax (μ m)).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr22 y).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          rewrite <- functor_comp.
          apply maponpaths.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (make_BinCoproduct
                      _ _ _ _ _ _
                      (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
        }
        rewrite functor_comp.
        rewrite !assoc'.
        apply maponpaths.
        apply (BinCoproductIn2Commutes
                 _ _ _
                 (make_BinCoproduct
                    _ _ _ _ _ _
                    (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y)))))).
    Qed.

    Definition bincoproduct_obj_eilenberg_moore
               (x y : eilenberg_moore_cat m)
      : eilenberg_moore_cat m.
    Proof.
      use make_ob_eilenberg_moore.
      - exact (bincoproduct_obj_eilenberg_moore_ob x y).
      - exact (bincoproduct_obj_eilenberg_moore_ob_mor x y).
      - exact (bincoproduct_obj_eilenberg_moore_ob_unit x y).
      - exact (bincoproduct_obj_eilenberg_moore_ob_mult x y).
    Defined.

    Definition bincoproduct_eilenberg_moore_in1
               (x y : eilenberg_moore_cat m)
      : x --> bincoproduct_obj_eilenberg_moore x y.
    Proof.
      use make_mor_eilenberg_moore.
      - apply BinCoproductIn1.
      - abstract
          (refine (!_) ;
           apply (BinCoproductIn1Commutes
                    _ _ _
                    (make_BinCoproduct
                       _ _ _ _ _ _
                       (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y))))))).
    Defined.

    Definition bincoproduct_eilenberg_moore_in2
               (x y : eilenberg_moore_cat m)
      : y --> bincoproduct_obj_eilenberg_moore x y.
    Proof.
      use make_mor_eilenberg_moore.
      - apply BinCoproductIn2.
      - abstract
          (refine (!_) ;
           apply (BinCoproductIn2Commutes
                    _ _ _
                    (make_BinCoproduct
                       _ _ _ _ _ _
                       (Hm _ _ _ _ _ (pr2 (P (pr11 x) (pr11 y))))))).
    Defined.

    Definition bincoproducts_eilenberg_moore
      : BinCoproducts (eilenberg_moore_cat m).
    Proof.
      intros x y.
      use make_BinCoproduct.
      - exact (bincoproduct_obj_eilenberg_moore x y).
      - exact (bincoproduct_eilenberg_moore_in1 x y).
      - exact (bincoproduct_eilenberg_moore_in2 x y).
      - use isBinCoproduct_eilenberg_moore.
        + exact Hm.
        + exact (pr2 (P (pr11 x) (pr11 y))).
    Defined.

    Definition eilenberg_moore_pr_preserves_bincoproduct
      : preserves_bincoproduct (eilenberg_moore_pr m).
    Proof.
      use preserves_bincoproduct_if_preserves_chosen.
      - exact bincoproducts_eilenberg_moore.
      - intros x y.
        apply P.
    Defined.

    Definition functor_to_eilenberg_moore_cat_preserves_bincoproduct
               {C' : category}
               (F : C' ⟶ C)
               (HF : preserves_bincoproduct F)
               (α : F ∙ m ⟹ functor_identity C' ∙ F)
               (p₁ : ∏ (x : C'), η m (F x) · α x = identity (functor_identity C (F x)))
               (p₂ : ∏ (x : C'), # m (α x) · α x = μ m (F x) · α x)
      : preserves_bincoproduct (functor_to_eilenberg_moore_cat m F α p₁ p₂).
    Proof.
      intros x y p π₁ π₂ Hx.
      use isBinCoproduct_eilenberg_moore.
      - exact Hm.
      - apply HF.
        exact Hx.
    Defined.
  End BinaryCoproducts.
End EilenbergMooreCategoryLimits.
