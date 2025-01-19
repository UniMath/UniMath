(**************************************************************************************

 Parameterized natural numbers object in the slice category

 If some category with finite limits has a parameterized natural numbers object, then
 each slice also has a natural numbers object. We also show that the parameterized
 natural is stable under substitution and that the functor arising from the
 pseudofunctoriality of the arrow category preserves parameterized natural numbers
 objects. The main work lies in verifying that the necessary functors preserves
 parameterized natural number objects. Here the idea is to calculate the preservation
 morphism and prove that it is equal to some morphism of which one can directly see
 that it is an isomorphism.

 Content
 1. Basic definitions
 2. The universal mapping property
 3. Parameterized natural numbers object in the slice category
 4. Stability under substitution
 5. Preservation by the pseudofunctoriality of the arrow category

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.

Local Open Scope cat.

Section CodNNO.
  Context {C : category}
          {T : Terminal C}
          {BC : BinProducts C}
          (N : parameterized_NNO T BC)
          (PC : Pullbacks C)
          (x : C).

  (** * 1. Basic definitions *)
  Definition slice_parameterized_NNO_ob
    : C/x
    := pr_cod_fib BC x N.

  Definition slice_parameterized_NNO_Z
    : codomain_fib_terminal x --> slice_parameterized_NNO_ob.
  Proof.
    use make_cod_fib_mor.
    - exact (BinProductArrow
               _ _
               (identity _)
               (TerminalArrow _ _ · parameterized_NNO_Z N)).
    - abstract
        (apply BinProductPr1Commutes).
  Defined.

  Definition slice_parameterized_NNO_S
    : slice_parameterized_NNO_ob --> slice_parameterized_NNO_ob.
  Proof.
    use make_cod_fib_mor.
    - exact (BinProductOfArrows
               _ _ _
               (identity _)
               (parameterized_NNO_S N)).
    - abstract
        (cbn ;
         rewrite BinProductOfArrowsPr1 ;
         apply id_right).
  Defined.

  (** * 2. The universal mapping property *)
  Section UMP.
    Context {b y : C/x}
            (zy : b --> y)
            (sy : y --> y).

    Local Definition slice_parameterized_NNO_mor_dom
      : C/x.
    Proof.
      use make_cod_fib_ob.
      - exact (BC (cod_dom b) N).
      - exact (BinProductPr1 _ _ · cod_mor b).
    Defined.

    Let d : C/x
      := slice_parameterized_NNO_mor_dom.

    Local Definition slice_parameterized_NNO_mor_dom_iso_map
      : d --> codomain_fib_binproducts PC x b slice_parameterized_NNO_ob.
    Proof.
      use make_cod_fib_mor.
      - use PullbackArrow ; cbn.
        + exact (BinProductPr1 _ _).
        + exact (BinProductOfArrows _ _ _ (cod_mor b) (identity _)).
        + abstract
            (rewrite BinProductOfArrowsPr1 ;
             apply idpath).
      - abstract
          (cbn ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr1 ;
           apply idpath).
    Defined.

    Arguments slice_parameterized_NNO_mor_dom_iso_map /.

    Local Definition slice_parameterized_NNO_mor_dom_iso_inv
      : cod_dom (codomain_fib_binproducts PC x b slice_parameterized_NNO_ob)
        -->
        cod_dom d.
    Proof.
      use BinProductArrow.
      - apply PullbackPr1.
      - exact (PullbackPr2 _ · BinProductPr2 _ _).
    Defined.

    Arguments slice_parameterized_NNO_mor_dom_iso_inv /.

    Local Proposition is_z_iso_slice_parameterized_NNO_mor_dom_iso_are_invs
      : is_inverse_in_precat
          (dom_mor slice_parameterized_NNO_mor_dom_iso_map)
          slice_parameterized_NNO_mor_dom_iso_inv.
    Proof.
      unfold slice_parameterized_NNO_mor_dom_iso_inv.
      split.
      - use BinProductArrowsEq ; cbn.
        + rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr2.
          rewrite BinProductOfArrowsPr2.
          rewrite id_left, id_right.
          apply idpath.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite BinProductPr1Commutes.
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          use BinProductArrowsEq ; cbn.
          * rewrite !assoc'.
            rewrite BinProductOfArrowsPr1.
            rewrite !assoc.
            rewrite BinProductPr1Commutes.
            rewrite id_left.
            apply PullbackSqrCommutes.
          * rewrite !assoc'.
            rewrite BinProductOfArrowsPr2.
            rewrite !assoc.
            rewrite BinProductPr2Commutes.
            rewrite id_left, id_right.
            apply idpath.
    Qed.

    Local Definition is_z_iso_slice_parameterized_NNO_mor_dom_iso_map
      : is_z_isomorphism (dom_mor slice_parameterized_NNO_mor_dom_iso_map).
    Proof.
      use make_is_z_isomorphism.
      - exact slice_parameterized_NNO_mor_dom_iso_inv.
      - exact is_z_iso_slice_parameterized_NNO_mor_dom_iso_are_invs.
    Defined.

    Local Definition slice_parameterized_NNO_mor_dom_iso
      : z_iso d (codomain_fib_binproducts PC x b slice_parameterized_NNO_ob).
    Proof.
      refine (slice_parameterized_NNO_mor_dom_iso_map ,, _).
      use make_is_z_isomorphism.
      - use make_cod_fib_mor.
        + apply slice_parameterized_NNO_mor_dom_iso_inv.
        + abstract
            (cbn ;
             rewrite !assoc ;
             rewrite BinProductPr1Commutes ;
             apply idpath).
      - abstract
          (split ;
           use eq_mor_cod_fib ;
           rewrite comp_in_cod_fib ;
           apply is_z_iso_slice_parameterized_NNO_mor_dom_iso_are_invs).
    Defined.

    Arguments slice_parameterized_NNO_mor_dom_iso /.

    Definition slice_parameterized_NNO_mor_mor
      : cod_dom d --> cod_dom y.
    Proof.
      use parameterized_NNO_mor.
      - exact (dom_mor zy).
      - exact (dom_mor sy).
    Defined.

    Proposition slice_parameterized_NNO_mor_eq
      : slice_parameterized_NNO_mor_mor · cod_mor y = cod_mor d.
    Proof.
      unfold slice_parameterized_NNO_mor_mor ; cbn.
      use parameterized_NNO_mor_unique.
      - exact (cod_mor b).
      - apply identity.
      - rewrite !assoc.
        rewrite parameterized_NNO_mor_Z.
        apply (mor_eq zy).
      - rewrite !assoc.
        rewrite parameterized_NNO_mor_S.
        rewrite id_right.
        rewrite !assoc'.
        apply maponpaths.
        apply (mor_eq sy).
      - rewrite !assoc.
        rewrite BinProductPr1Commutes.
        apply id_left.
      - rewrite !assoc.
        rewrite BinProductOfArrowsPr1.
        rewrite !id_right.
        apply idpath.
    Qed.

    Definition slice_parameterized_NNO_mor
      : codomain_fib_binproducts PC x b slice_parameterized_NNO_ob --> y.
    Proof.
      refine (inv_from_z_iso slice_parameterized_NNO_mor_dom_iso · _).
      use make_cod_fib_mor.
      - exact slice_parameterized_NNO_mor_mor.
      - exact slice_parameterized_NNO_mor_eq.
    Defined.

    Proposition slice_parameterized_NNO_mor_Z
      : BinProductArrow
          _ _
          (identity b)
          (TerminalArrow (codomain_fib_terminal x) b · slice_parameterized_NNO_Z)
        · slice_parameterized_NNO_mor
        =
        zy.
    Proof.
      unfold slice_parameterized_NNO_mor.
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      rewrite !assoc.
      refine (_ @ parameterized_NNO_mor_Z N _ _ (dom_mor zy) (dom_mor sy)).
      apply maponpaths_2.
      use BinProductArrowsEq.
      - rewrite BinProductPr1Commutes.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        etrans.
        {
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        apply idpath.
      - rewrite BinProductPr2Commutes.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr2Commutes.
        }
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        rewrite comp_in_cod_fib.
        cbn.
        rewrite !id_right.
        rewrite !assoc'.
        rewrite BinProductPr2Commutes.
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
    Qed.

    Proposition slice_parameterized_NNO_mor_S
      : BinProductOfArrows
          _ _ _
          (identity b)
          slice_parameterized_NNO_S
        · slice_parameterized_NNO_mor
        =
        slice_parameterized_NNO_mor · sy.
    Proof.
      unfold slice_parameterized_NNO_mor.
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      refine (!_).
      etrans.
      {
        cbn.
        rewrite !assoc'.
        apply maponpaths.
        exact (!(parameterized_NNO_mor_S N _ _ (dom_mor zy) (dom_mor sy))).
      }
      rewrite !assoc.
      apply maponpaths_2.
      use BinProductArrowsEq.
      - rewrite !assoc'.
        rewrite BinProductOfArrowsPr1.
        rewrite id_right.
        rewrite BinProductPr1Commutes.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        etrans.
        {
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        rewrite id_right.
        apply idpath.
      - rewrite !assoc'.
        rewrite BinProductOfArrowsPr2.
        rewrite !assoc.
        rewrite BinProductPr2Commutes.
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply BinProductPr2Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        rewrite !comp_in_cod_fib ; cbn.
        rewrite !assoc'.
        rewrite BinProductOfArrowsPr2.
        apply idpath.
    Qed.

    Local Lemma slice_parameterized_NNO_unique_Z
                (f : codomain_fib_binproducts PC x b slice_parameterized_NNO_ob --> y)
                (fz : BinProductArrow
                        _ _
                        (identity b)
                        (TerminalArrow (codomain_fib_terminal x) b
                         · slice_parameterized_NNO_Z)
                      · f
                      =
                        zy)
      : BinProductArrow
          _ _
          (identity _)
          (TerminalArrow T (cod_dom b) · parameterized_NNO_Z N)
        · (dom_mor slice_parameterized_NNO_mor_dom_iso · dom_mor f)
        =
        dom_mor zy.
    Proof.
      refine (_ @ maponpaths dom_mor fz).
      rewrite comp_in_cod_fib.
      rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        }
        etrans.
        {
          apply BinProductPr1Commutes.
        }
        refine (!_).
        etrans.
        {
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        apply idpath.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr2.
        }
        refine (!_).
        etrans.
        {
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        rewrite comp_in_cod_fib.
        cbn.
        rewrite id_right.
        use BinProductArrowsEq.
        + rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          rewrite id_right.
          rewrite BinProductOfArrowsPr1.
          rewrite !assoc.
          rewrite BinProductPr1Commutes.
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          rewrite BinProductOfArrowsPr2.
          rewrite !assoc.
          rewrite BinProductPr2Commutes.
          rewrite id_right.
          apply maponpaths_2.
          apply TerminalArrowEq.
    Qed.

    Local Lemma slice_parameterized_NNO_unique_S
                (f : codomain_fib_binproducts PC x b slice_parameterized_NNO_ob --> y)
                (fs : BinProductOfArrows
                        _ _ _
                        (identity b)
                        slice_parameterized_NNO_S
                      · f
                      =
                      f · sy)
      : BinProductOfArrows
          _ _ _
          (identity (cod_dom b))
          (parameterized_NNO_S N)
        · (dom_mor slice_parameterized_NNO_mor_dom_iso · dom_mor f)
        =
        dom_mor slice_parameterized_NNO_mor_dom_iso
        · dom_mor f
        · dom_mor sy.
    Proof.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        refine (_ @ !(maponpaths dom_mor fs)).
        rewrite comp_in_cod_fib.
        apply idpath.
      }
      rewrite comp_in_cod_fib.
      rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        rewrite id_right.
        etrans.
        {
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (PC _ _ _ _ _)).
        }
        etrans.
        {
          apply BinProductOfArrowsPr1.
        }
        apply id_right.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        rewrite comp_in_cod_fib.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (PC _ _ _ _ _)).
        }
        cbn.
        rewrite !BinProductOfArrows_comp.
        rewrite !id_left, !id_right.
        apply idpath.
    Qed.

    Proposition slice_parameterized_NNO_unique
      : isaprop
          (∑ (f : codomain_fib_binproducts PC x b slice_parameterized_NNO_ob --> y),
           (BinProductArrow
              _ _
              (identity b)
              (TerminalArrow (codomain_fib_terminal x) b · slice_parameterized_NNO_Z)
            · f
            =
            zy)
           ×
           (BinProductOfArrows _ _ _  (identity b) slice_parameterized_NNO_S · f
            =
            f · sy)).
    Proof.
      use invproofirrelevance.
      intros f₁ f₂.
      use subtypePath.
      {
        intro.
        use isapropdirprod ; apply homset_property.
      }
      use (cancel_precomposition_z_iso slice_parameterized_NNO_mor_dom_iso).
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      use parameterized_NNO_mor_unique.
      - exact (dom_mor zy).
      - exact (dom_mor sy).
      - apply slice_parameterized_NNO_unique_Z.
        exact (pr12 f₁).
      - apply slice_parameterized_NNO_unique_S.
        exact (pr22 f₁).
      - apply slice_parameterized_NNO_unique_Z.
        exact (pr12 f₂).
      - apply slice_parameterized_NNO_unique_S.
        exact (pr22 f₂).
    Qed.
  End UMP.

  (** * 3. Parameterized natural numbers object in the slice category *)
  Definition slice_parameterized_NNO
    : parameterized_NNO
        (codomain_fib_terminal x)
        (codomain_fib_binproducts PC x).
  Proof.
    use make_parameterized_NNO.
    - exact slice_parameterized_NNO_ob.
    - exact slice_parameterized_NNO_Z.
    - exact slice_parameterized_NNO_S.
    - intros b y zy sy.
      use iscontraprop1.
      + apply slice_parameterized_NNO_unique.
      + simple refine (_ ,, _ ,, _).
        * exact (slice_parameterized_NNO_mor zy sy).
        * apply slice_parameterized_NNO_mor_Z.
        * apply slice_parameterized_NNO_mor_S.
  Defined.
End CodNNO.

(** * 4. Stability under substitution *)
Section Stable.
  Context {C : category}
          {T : Terminal C}
          {BC : BinProducts C}
          (N : parameterized_NNO T BC)
          (PC : Pullbacks C)
          {x y : C}
          (f : x --> y).

  Definition slice_parameterized_NNO_stable_mor
    : BC x N --> PC y (BC y N) x (BinProductPr1 C (BC y N)) f.
  Proof.
    use PullbackArrow.
    - refine (BinProductOfArrows _ _ _ f (identity _)).
    - apply BinProductPr1.
    - abstract (apply BinProductOfArrowsPr1).
  Defined.

  Definition slice_parameterized_NNO_stable_inv
    : PC y (BC y N) x (BinProductPr1 C (BC y N)) f --> BC x N.
  Proof.
    use BinProductArrow.
    - apply PullbackPr2.
    - exact (PullbackPr1 _ · BinProductPr2 _ _).
  Defined.

  Proposition slice_parameterized_NNO_stable_is_z_iso_inverses
    : is_inverse_in_precat
        slice_parameterized_NNO_stable_mor
        slice_parameterized_NNO_stable_inv.
  Proof.
    unfold slice_parameterized_NNO_stable_mor, slice_parameterized_NNO_stable_inv.
    split.
    - use BinProductArrowsEq.
      + rewrite id_left.
        rewrite !assoc'.
        rewrite BinProductPr1Commutes.
        apply PullbackArrow_PullbackPr2.
      + rewrite id_left.
        rewrite !assoc'.
        rewrite BinProductPr2Commutes.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite BinProductOfArrowsPr2.
        apply id_right.
    - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))).
      + rewrite id_left.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        use BinProductArrowsEq.
        * rewrite !assoc'.
          rewrite BinProductOfArrowsPr1.
          rewrite !assoc.
          rewrite BinProductPr1Commutes.
          refine (!_).
          apply PullbackSqrCommutes.
        * rewrite !assoc'.
          rewrite BinProductOfArrowsPr2.
          rewrite id_right.
          rewrite BinProductPr2Commutes.
          apply idpath.
      + rewrite id_left.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite BinProductPr1Commutes.
        apply idpath.
  Qed.

  Definition slice_parameterized_NNO_stable_is_z_iso
    : is_z_isomorphism slice_parameterized_NNO_stable_mor.
  Proof.
    use make_is_z_isomorphism.
    - exact slice_parameterized_NNO_stable_inv.
    - exact slice_parameterized_NNO_stable_is_z_iso_inverses.
  Defined.

  Proposition slice_parameterized_NNO_eq
    : slice_parameterized_NNO_stable_mor
      =
      dom_mor
        (preserves_parameterized_NNO_mor
           (slice_parameterized_NNO N PC y)
           (slice_parameterized_NNO N PC x)
           (cod_pb PC f)
           (codomain_fib_preserves_terminal PC f)).
  Proof.
    unfold slice_parameterized_NNO_stable_mor.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))).
    - rewrite PullbackArrow_PullbackPr1.
      use BinProductArrowsEq.
      + etrans.
        {
          apply BinProductOfArrowsPr1.
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackSqrCommutes.
        }
        rewrite !assoc.
        apply maponpaths_2.
        exact (mor_eq
                 (preserves_parameterized_NNO_mor
                    (slice_parameterized_NNO N PC y)
                    (slice_parameterized_NNO N PC x)
                    (cod_pb PC f)
                    (codomain_fib_preserves_terminal PC f))).
      + etrans.
        {
          apply BinProductOfArrowsPr2.
        }
        rewrite id_right.
        refine (!_).
        rewrite !assoc'.
        use parameterized_NNO_mor_unique.
        * exact (TerminalArrow T x · parameterized_NNO_Z N).
        * exact (parameterized_NNO_S N).
        * pose (maponpaths
                  dom_mor
                  (preserves_parameterized_NNO_mor_Z
                     (slice_parameterized_NNO N PC y)
                     (slice_parameterized_NNO N PC x)
                     (cod_pb PC f)
                     (codomain_fib_preserves_terminal PC f)))
            as p.
          rewrite !comp_in_cod_fib in p.
          rewrite cod_fiber_functor_on_mor in p.
          etrans.
          {
            rewrite !assoc.
            do 2 apply maponpaths_2.
            exact p.
          }
          clear p.
          cbn.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite PullbackArrow_PullbackPr1.
            rewrite !assoc'.
            rewrite BinProductPr2Commutes.
            apply idpath.
          }
          rewrite !assoc.
          apply maponpaths_2.
          apply TerminalArrowEq.
        * pose (maponpaths
                  dom_mor
                  (preserves_parameterized_NNO_mor_S
                     (slice_parameterized_NNO N PC y)
                     (slice_parameterized_NNO N PC x)
                     (cod_pb PC f)
                     (codomain_fib_preserves_terminal PC f)))
            as p.
          rewrite !comp_in_cod_fib in p.
          rewrite cod_fiber_functor_on_mor in p.
          etrans.
          {
            rewrite !assoc.
            do 2 apply maponpaths_2.
            exact p.
          }
          clear p.
          rewrite !assoc'.
          apply maponpaths.
          cbn.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc'.
          rewrite BinProductOfArrowsPr2.
          apply idpath.
        * rewrite BinProductPr2Commutes.
          apply idpath.
        * rewrite BinProductOfArrowsPr2.
          apply idpath.
    - rewrite PullbackArrow_PullbackPr2.
      refine (!_).
      exact (mor_eq
               (preserves_parameterized_NNO_mor
                  (slice_parameterized_NNO N PC y)
                  (slice_parameterized_NNO N PC x)
                  (cod_pb PC f)
                  (codomain_fib_preserves_terminal PC f))).
  Qed.

  Definition slice_parameterized_NNO_stable
    : preserves_parameterized_NNO
        (slice_parameterized_NNO N PC y)
        (slice_parameterized_NNO N PC x)
        _
        (codomain_fib_preserves_terminal PC f).
  Proof.
    unfold preserves_parameterized_NNO.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    use is_z_isomorphism_path.
    - exact slice_parameterized_NNO_stable_mor.
    - exact slice_parameterized_NNO_eq.
    - exact slice_parameterized_NNO_stable_is_z_iso.
  Defined.
End Stable.

(** * 5. Preservation by the pseudofunctoriality of the arrow category *)
Section Preservation.
  Context {C₁ C₂ : category}
          {T₁ : Terminal C₁}
          {BC₁ : BinProducts C₁}
          (N₁ : parameterized_NNO T₁ BC₁)
          (PC₁ : Pullbacks C₁)
          {T₂ : Terminal C₂}
          {BC₂ : BinProducts C₂}
          (N₂ : parameterized_NNO T₂ BC₂)
          (PC₂ : Pullbacks C₂)
          {F : C₁ ⟶ C₂}
          (HF : preserves_terminal F)
          (HF' : preserves_binproduct F)
          (HFN : preserves_parameterized_NNO N₁ N₂ F HF)
          (x : C₁).

  Definition codomain_functor_preserves_parameterized_NNO_mor
    : BC₂ (F x) N₂ --> F (BC₁ x N₁)
    := BinProductOfArrows
         _ _ _
         (identity _)
         (preserves_parameterized_NNO_mor N₁ N₂ _ HF)
       · inv_from_z_iso
           (preserves_binproduct_to_z_iso F HF' (BC₁ x N₁) (BC₂ (F x) (F N₁))).

  Definition codomain_functor_preserves_parameterized_NNO_iso
    : is_z_isomorphism
        (BinProductOfArrows
           _ (BC₂ (F x) (F N₁)) (BC₂ (F x) N₂)
           (identity (F x))
           (preserves_parameterized_NNO_mor N₁ N₂ F HF)).
  Proof.
    use make_is_z_isomorphism.
    - exact (BinProductOfArrows _ _ _ (identity _) (is_z_isomorphism_mor HFN)).
    - abstract
        (split ;
         rewrite BinProductOfArrows_comp ;
         rewrite id_left ;
         refine (_ @ BinProductOfArrows_id _ _ _ _) ;
         apply maponpaths ;
         apply HFN).
  Defined.

  Proposition codomain_functor_preserves_parameterized_NNO_eq
    : codomain_functor_preserves_parameterized_NNO_mor
      =
      dom_mor
        (preserves_parameterized_NNO_mor
           (slice_parameterized_NNO N₁ PC₁ x)
           (slice_parameterized_NNO N₂ PC₂ (F x))
           (fiber_functor (disp_codomain_functor F) x)
           (preserves_terminal_fiber_disp_codomain_functor F x)).
  Proof.
    use (BinProductArrowsEq _ _ _ (preserves_binproduct_to_binproduct _ HF' (BC₁ x N₁))).
    - etrans.
      {
        unfold codomain_functor_preserves_parameterized_NNO_mor.
        rewrite !assoc'.
        apply maponpaths.
        apply BinProductPr1Commutes.
      }
      rewrite BinProductOfArrowsPr1.
      rewrite id_right.
      refine (!_).
      exact (mor_eq
               (preserves_parameterized_NNO_mor
                  (slice_parameterized_NNO N₁ PC₁ x)
                  (slice_parameterized_NNO N₂ PC₂ (F x))
                  (fiber_functor (disp_codomain_functor F) x)
                  (preserves_terminal_fiber_disp_codomain_functor F x))).
    - etrans.
      {
        unfold codomain_functor_preserves_parameterized_NNO_mor.
        rewrite !assoc'.
        apply maponpaths.
        apply BinProductPr2Commutes.
      }
      rewrite BinProductOfArrowsPr2.
      refine (!_).
      use parameterized_NNO_mor_unique.
      + exact (#F (TerminalArrow _ x · parameterized_NNO_Z N₁)).
      + exact (#F (parameterized_NNO_S N₁)).
      + pose (maponpaths
                dom_mor
                (preserves_parameterized_NNO_mor_Z
                   (slice_parameterized_NNO N₁ PC₁ x)
                   (slice_parameterized_NNO N₂ PC₂ (F x))
                   (fiber_functor (disp_codomain_functor F) x)
                   (preserves_terminal_fiber_disp_codomain_functor F x)))
          as p.
        rewrite !comp_in_cod_fib in p.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          exact p.
        }
        clear p.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply disp_codomain_fiber_functor_mor.
        }
        cbn.
        rewrite !id_left.
        rewrite functor_id.
        rewrite id_left.
        rewrite <- functor_comp.
        apply maponpaths.
        apply BinProductPr2Commutes.
      + pose (maponpaths
                dom_mor
                (preserves_parameterized_NNO_mor_S
                   (slice_parameterized_NNO N₁ PC₁ x)
                   (slice_parameterized_NNO N₂ PC₂ (F x))
                   (fiber_functor (disp_codomain_functor F) x)
                   (preserves_terminal_fiber_disp_codomain_functor F x)))
          as p.
        rewrite !comp_in_cod_fib in p.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          exact p.
        }
        clear p.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply disp_codomain_fiber_functor_mor.
        }
        cbn.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply BinProductOfArrowsPr2.
      + rewrite !assoc.
        rewrite BinProductPr2Commutes.
        rewrite !assoc'.
        rewrite preserves_parameterized_NNO_mor_Z.
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
      + rewrite !assoc.
        rewrite BinProductOfArrowsPr2.
        rewrite !assoc'.
        rewrite preserves_parameterized_NNO_mor_S.
        apply idpath.
  Qed.

  Definition codomain_functor_preserves_parameterized_NNO
    : preserves_parameterized_NNO
        (slice_parameterized_NNO N₁ PC₁ x)
        (slice_parameterized_NNO N₂ PC₂ (F x))
        _
        (preserves_terminal_fiber_disp_codomain_functor F x).
  Proof.
    unfold preserves_parameterized_NNO.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    use is_z_isomorphism_path.
    - exact codomain_functor_preserves_parameterized_NNO_mor.
    - exact codomain_functor_preserves_parameterized_NNO_eq.
    - use is_z_isomorphism_comp.
      + exact codomain_functor_preserves_parameterized_NNO_iso.
      + apply is_z_iso_inv_from_z_iso.
  Defined.
End Preservation.
