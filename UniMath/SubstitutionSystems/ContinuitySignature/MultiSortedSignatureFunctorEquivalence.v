Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section B.

  Lemma make_isBinProduct'
        {C : category} {x y : C}
        (Pxy : BinProduct _ x y)
        (z : C) (zx : C⟦z,x⟧) (zy : C⟦z,y⟧) :
        (∑ i : is_z_isomorphism (BinProductArrow C Pxy zx zy),
            pr1 i · zx = BinProductPr1 _ Pxy × pr1 i · zy = BinProductPr2 _ Pxy)
          -> isBinProduct C x y z zx zy.
  Proof.
    intros [i [px py]].
    use make_isBinProduct.
    intros c f g.
    use tpair.
    - exists (BinProductArrow _ Pxy f g · pr1 i).
      split.
      + etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, px.
        apply BinProductPr1Commutes.
      + etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, py.
        apply BinProductPr2Commutes.
    - intro co.
      use total2_paths_f.
      + apply pathsinv0.
        use (z_iso_inv_to_right _ _ _ _ (z_iso_inv (_,,i))).
        apply pathsinv0.
        use BinProductArrowUnique.
        * etrans.
          1: apply assoc'.
          etrans.
          1: apply maponpaths, BinProductPr1Commutes.
          exact (pr12 co).
        * etrans.
          1: apply assoc'.
          etrans.
          1: apply maponpaths, BinProductPr2Commutes.
          exact (pr22 co).
      + use total2_paths_f ; apply homset_property.
  Defined.

  Definition coproducts_commute_binproducts_mor
             {C : category} (BP : BinProducts C) {I : UU}
             (CP : Coproducts I C) (x y : C)
    : C⟦CP (λ p : I, BP x y), BP (CP (λ p : I, x)) (CP (λ p : I, y))⟧.
  Proof.
    use BinProductArrow ; use CoproductOfArrows.
    - exact (λ i, BinProductPr1 C (BP x y)).
    - exact (λ i, BinProductPr2 C (BP x y)).
  Defined.

  Definition propcoproducts_commute_binproducts
             (C : category) (BP : BinProducts C) (pcp : ∏ p : hProp, Coproducts p C)
               : UU
    := ∏ p : hProp, ∏ x y : C, is_z_isomorphism (coproducts_commute_binproducts_mor BP (pcp p) x y).

End B.

Section A.

  Definition post_comp_functor_of_comp
             {A B C D E : category}
             (F : functor A [B,C])
             (G : functor C D)
             (H : functor D E)
    : nat_z_iso (functor_composite F (post_comp_functor (functor_composite G H)))
                (functor_composite (functor_composite F (post_comp_functor G)) (post_comp_functor H)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; apply nat_trans_id.
      + intro ; intros.
        use nat_trans_eq.
        { apply homset_property. }
        exact (λ _, id_right _ @ ! id_left _).
    - intro.
      use make_is_z_isomorphism.
      + apply nat_trans_id.
      + split ; (use nat_trans_eq ; [apply homset_property | intro ; apply id_right]).
  Defined.

  Definition BinProduct_of_functors_distr
             {C D E : category}
             (F G : functor C D) (H : functor D E)
             (Hp : preserves_binproduct H)
             (BPD : BinProducts D)
           (BPE : BinProducts E)
    : nat_z_iso (functor_composite (BinProduct_of_functors BPD F G) H)
                (BinProduct_of_functors BPE (functor_composite F H) (functor_composite G H)).
  Proof.
    set (P := λ c, make_BinProduct _ _ _ _ _ _ (Hp (F c) (G c) _ _ _ (pr2 (BPD (F c) (G c))))).
    set (i := λ c, iso_between_BinProduct (P c) (BPE (H (F c)) (H (G c)))).

    use make_nat_z_iso.
    - use make_nat_trans.
      + intro c.
        apply (i c).
      + intro ; intros.
        use (z_iso_inv_to_right _ _ _ _ (i x')).
        etrans.
        2: {
          apply maponpaths_2.
          apply pathsinv0, (postcompWithBinProductArrow).
        }
        cbn.
        use pathscomp0.
        * exact (BinProductArrow _ (P x')  (#H (pr121 (BPD (F x) (G x)) · # F f)) (#H (pr221 (BPD (F x) (G x)) · # G f))).
        * use (BinProductArrowUnique _ _ _ (P x')).
          -- etrans.
             1: apply pathsinv0, functor_comp.
             apply maponpaths, BinProductPr1Commutes.
          -- etrans.
             1: apply pathsinv0, functor_comp.
             apply maponpaths, BinProductPr2Commutes.
        * apply pathsinv0.
          use (BinProductArrowUnique _ _ _ (P x')).
          -- etrans.
             1: apply assoc'.
             etrans.
             1: apply maponpaths, (BinProductPr1Commutes _ _ _ (P x')).
             etrans.
             1: apply BinProductPr1Commutes.
             apply pathsinv0, functor_comp.
          -- etrans.
             1: apply assoc'.
             etrans.
             1: apply maponpaths, (BinProductPr2Commutes _ _ _ (P x')).
             etrans.
             1: apply BinProductPr2Commutes.
             apply pathsinv0, functor_comp.
    - intro c.
      apply (i c).
  Defined.

  Lemma BinProductArrowId
        {C : category} {c d : C} (P : BinProduct C c d)
    : identity _ = BinProductArrow C P (BinProductPr1 C P) (BinProductPr2 C P).
  Proof.
    refine (BinProductArrowEta _ _ _ P _ (identity _) @ _).
    etrans.
    1: apply maponpaths_2, id_left.
    apply maponpaths, id_left.
  Qed.

  Definition isBinProduct_is_objectwise
             {C D : category}
             {F1 F2 P : [C, D]}
             {P1 : [C, D] ⟦ P, F1 ⟧}
             {P2 : [C, D] ⟦ P, F2 ⟧}
             (Pc_prod : ∏ c: C, isBinProduct D (pr1 F1 c) (pr1 F2 c) (pr1 P c) (pr1 P1 c) (pr1 P2 c))
    : BinProducts D -> isBinProduct [C, D] F1 F2 P P1 P2.
  Proof.
    intro BP.
    use make_isBinProduct'.
    { apply functor_precat_binproduct_cone ; exact BP. }
    use tpair.
    - use nat_trafo_z_iso_if_pointwise_z_iso.
      intro c.
      set (Pc := make_BinProduct _ _ _ _ _ _ (Pc_prod c)).
      use make_is_z_isomorphism.
      + use (BinProductArrow _ Pc).
        * apply BinProductPr1.
        * apply BinProductPr2.
      + split.
        * etrans.
          1: apply (precompWithBinProductArrow D Pc).

          etrans.
          1: apply maponpaths, BinProductPr2Commutes.
          etrans.
          1: apply maponpaths_2, BinProductPr1Commutes.
          exact (! BinProductArrowId Pc).
        * etrans.
          1: apply (precompWithBinProductArrow D (BP _ _)).
          etrans.
          1: apply maponpaths, (BinProductPr2Commutes D _ _ Pc).
          etrans.
          1: apply maponpaths_2, (BinProductPr1Commutes D _ _ Pc).
          exact (! BinProductArrowId (BP _ _)).
    - split.
      + use nat_trans_eq.
        { apply homset_property. }
        intro c.
        set (Pc := make_BinProduct _ _ _ _ _ _ (Pc_prod c)).
        apply (BinProductPr1Commutes D _ _ Pc).
      + use nat_trans_eq.
        { apply homset_property. }
        intro c.
        set (Pc := make_BinProduct _ _ _ _ _ _ (Pc_prod c)).
        apply (BinProductPr2Commutes D _ _ Pc).
  Defined.

  Definition isBinProduct_to_objectwise
             {C D : category}
             {F1 F2 P : [C, D]}
             {P1 : [C, D] ⟦ P, F1 ⟧}
             {P2 : [C, D] ⟦ P, F2 ⟧}
             (P_prod : isBinProduct [C, D] F1 F2 P P1 P2)
             (BP : BinProducts D) (c : C)
    : isBinProduct D (pr1 F1 c) (pr1 F2 c) (pr1 P c) (pr1 P1 c) (pr1 P2 c).
  Proof.
    use make_isBinProduct'.
    { apply BP. }

    set (i := iso_between_BinProduct
                (make_BinProduct _ _ _ _ _ _ P_prod)
                (functor_precat_binproduct_cone C D BP F1 F2)).
    set (ni := nat_z_iso_from_z_iso _ i).

    use tpair.
    { apply (pr2 ni c). }
    split.
    - set (p := BinProductPr1Commutes [C,D] _ _  (make_BinProduct [C, D] F1 F2 P P1 P2 P_prod)).
      set (p' := p _ (binproduct_nat_trans_pr1 C D BP F1 F2) (binproduct_nat_trans_pr2 C D BP F1 F2)).
      exact (eqtohomot (base_paths _ _ p') c).
    - set (p := BinProductPr2Commutes [C,D] _ _  (make_BinProduct [C, D] F1 F2 P P1 P2 P_prod)).
      set (p' := p _ (binproduct_nat_trans_pr1 C D BP F1 F2) (binproduct_nat_trans_pr2 C D BP F1 F2)).
      exact (eqtohomot (base_paths _ _ p') c).
  Defined.

  Definition post_comp_functor_preserves_binproduct
             (C : category) {D E : category} (F : functor D E)
             (BPD : BinProducts D)
             (BPE  : BinProducts E)
             (Fp : preserves_binproduct F)
    : preserves_binproduct (post_comp_functor (A := C) F).
  Proof.
    intros F1 F2 P P1 P2 P_prod.
    use (isBinProduct_is_objectwise _ BPE).
    intro c.
    apply Fp.
    exact (isBinProduct_to_objectwise P_prod BPD c).
  Defined.

  Definition BinProductOfArrows_is_z_iso
        {C : category}
        {a b : C} (Pab : BinProduct C a b)
        {c d : C} (Pcd : BinProduct C c d)
        (f : C ⟦ a, c ⟧) (g : C ⟦ b, d ⟧)
    : is_z_isomorphism f
      -> is_z_isomorphism g
      -> is_z_isomorphism (BinProductOfArrows C Pcd Pab f g)
    := λ pf pg, make_is_z_isomorphism _ _ (binproduct_of_z_iso_inv Pab Pcd (_,,pf) (_,,pg)).

  Definition nat_z_iso_BinProduct_of_functors
             {C D : category} (F1 F2 G1 G2 : functor C D)
             (BP : BinProducts D)
    : nat_z_iso F1 G1 -> nat_z_iso F2 G2
      -> nat_z_iso (BinProduct_of_functors BP F1 F2)
                  (BinProduct_of_functors BP G1 G2).
  Proof.
    intros α1 α2.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro c.
      use BinProductOfArrows.
        * apply α1.
        * apply α2.
      + intros x y f.
        etrans.
        1: apply postcompWithBinProductArrow.
        etrans.
        2: apply pathsinv0, postcompWithBinProductArrow.

        etrans.
        1: apply maponpaths_2, assoc'.
        etrans.
        1: apply maponpaths_2, maponpaths, (pr21 α1).

        etrans.
        2: apply maponpaths_2, assoc.
        apply maponpaths.
        etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, (pr21 α2).
        apply assoc.
    - intro.
      apply BinProductOfArrows_is_z_iso.
      + apply (pr2 α1).
      + apply (pr2 α2).
  Defined.


End A.

Section EquivalenceBetweenDifferentCharacterizationsOfMultiSortedSignatureToFunctor.

  Context (sort : UU) (Hsort_set : isaset sort) (C : category)
          (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

  Let Hsort := hlevelntosn 2 _ Hsort_set.
  (** Define the discrete category of sorts *)
  Let sort_cat : category := path_pregroupoid sort Hsort.

  (** This represents "sort → C" *)
  Let sortToC : category := [sort_cat,C].

  Goal sortToC = SortIndexing.sortToC sort Hsort C.
  Proof.
    apply idpath.
  Qed.

  Let BPsortToCC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

  Goal BPsortToCC = SortIndexing.BPsortToCC sort Hsort _ BP.
  Proof.
    apply idpath.
  Qed. (* slow *)

  Let TsortToCC : Terminal [sortToC,C] := Terminal_functor_precat _ _ TC.

  Goal TsortToCC = SortIndexing.TsortToCC sort Hsort _ TC.
  Proof.
    apply idpath.
  Qed. (* slow *)

  Let sortToC2 : category := [sortToC,sortToC].

  Goal sortToC2 = SortIndexing.sortToC2 sort Hsort C.
  Proof.
    apply idpath.
  Qed.

  Let hat_exp_functor_list'_piece0
      := hat_exp_functor_list'_piece sort Hsort C TC BC CC.

  Let hat_exp_functor_list0
      := hat_exp_functor_list sort Hsort C TC BP BC CC.
  Let hat_exp_functor_list'0
      := hat_exp_functor_list' sort Hsort C TC BP BC CC.
  Let hat_exp_functor_list'_optimized0
      := hat_exp_functor_list'_optimized sort Hsort C TC BP BC CC.

  Definition hat_exp_functor_list'_piece_test
             (xst : (list sort × sort) × sort)
    :  nat_z_iso
         (exp_functor sort Hsort C TC BC CC (pr1 xst)
                      ∙ post_comp_functor (hat_functor sort Hsort C CC (pr2 xst)))
         (hat_exp_functor_list'_piece0 xst).
  Proof.
    induction xst as [[x s] t].
    revert x.
    use list_ind.
    - simpl. (* This is necessary *)
      use make_nat_z_iso.
      + use make_nat_trans.
        * intro ; apply (nat_trans_id (C := sortToC) (C' := sortToC)).
        * intro ; intros.
          use nat_trans_eq.
          { exact (pr2 sortToC). }
          exact (λ _, id_right _ @ ! id_left _).
      + intro.
        use nat_trafo_z_iso_if_pointwise_z_iso.
        { apply (pr2 sortToC). }
        intro.
        apply identity_is_z_iso.
    - intro ; intros.
      use nat_z_iso_inv.
      apply post_comp_functor_of_comp.
  Defined.

  Definition hat_functor_preserves_binproducts (t : sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : preserves_binproduct (hat_functor sort Hsort C CC t).
  Proof.
    intros x y p p1 p2 p_prod.
    use (isBinProduct_is_objectwise _ BP).
    intro F.
    simpl.

    assert (ts_pr : isaprop (t = F)).
    { apply Hsort_set. }

    use make_isBinProduct'.
    { apply BP. }
    use tpair.
    - use make_is_z_isomorphism.
      + refine (_ · pr1 (c (_,,ts_pr) x y) · _).
        ++ use BinProductOfArrows ; use CoproductOfArrows ; intro ; apply identity.
        ++ use CoproductOfArrows.
           exact (λ _, BinProductOfArrows _ (make_BinProduct _ _ _ _ _ _ p_prod) (BP x y) (identity _) (identity _)).
      + split.
        * etrans.
          1: apply assoc.
          etrans.
          1: apply maponpaths_2, assoc.
          etrans.
          1: do 2 apply maponpaths_2 ; apply postcompWithBinProductArrow.

          transparent assert (ii : (is_z_isomorphism (CoproductOfArrows (t = F) C
      (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, BP x y))
      (CC (t = F) (Hsort t F) (λ _ : t = F, p))
      (λ _ : t = F,
       BinProductOfArrows C (make_BinProduct C x y p p1 p2 p_prod) (BP x y)
                          (identity x) (identity y))))).
          {
            apply CoproductOfArrowsIsos.
            intro.
            exact (BinProductOfArrows_is_z_iso (BP x y) (make_BinProduct C x y p p1 p2 p_prod) (identity _) (identity _) (identity_is_z_iso _) (identity_is_z_iso _)).
          }

          apply (z_iso_inv_to_right _ _ _ _ (_,,ii)).
          etrans.
          2: apply pathsinv0, id_left.
          apply pathsinv0.
          apply (z_iso_inv_on_left _ _ _ _ (_ ,, c ((t = F),, ts_pr) x y)).

          etrans.
          2: apply pathsinv0, precompWithBinProductArrow.
          use BinProductArrowUnique.
          -- etrans.
             1: apply BinProductPr1Commutes.
             simpl.
             unfold inv_from_z_iso.
             simpl.

             etrans.
             1: apply precompWithCoproductArrow.
             etrans.
             2: apply pathsinv0, precompWithCoproductArrow.
             use CoproductArrowUnique.
             intro.
             etrans.
             1: apply (CoproductInCommutes _ _ _ (CC (t = F) (Hsort t F) (λ _ : t = F, p))).
             etrans.
             2: apply assoc'.
             etrans.
             2: apply maponpaths_2, pathsinv0, BinProductPr1Commutes.
             apply assoc.
          -- etrans.
             1: apply BinProductPr2Commutes.
             simpl.
             unfold inv_from_z_iso.
             simpl.

             etrans.
             1: apply precompWithCoproductArrow.
             etrans.
             2: apply pathsinv0, precompWithCoproductArrow.
             use CoproductArrowUnique.
             intro.
             etrans.
             1: apply (CoproductInCommutes _ _ _ (CC (t = F) (Hsort t F) (λ _ : t = F, p))).
             etrans.
             2: apply assoc'.
             etrans.
             2: apply maponpaths_2, pathsinv0, BinProductPr2Commutes.
             apply assoc.
        * transparent assert (ii : (is_z_isomorphism (BinProductOfArrows C
    (BP (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, y)))
    (BP (CC (t = F) (Hsort t F) (λ _ : t = F, x)) (CC (t = F) (Hsort t F) (λ _ : t = F, y)))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, x))
       (λ _ : t = F, identity x))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, y))
       (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, y))
       (λ _ : t = F, identity y))))).
          {
            apply BinProductOfArrows_is_z_iso ;
              (apply CoproductOfArrowsIsos ; intro ; apply identity_is_z_iso).
          }

          rewrite ! assoc'.
          apply pathsinv0.
          apply (z_iso_inv_to_left _ _ _ ((_,,ii))).
          etrans.
          1: apply id_right.

          apply (z_iso_inv_to_left _ _ _ (z_iso_inv (_ ,, c ((t = F),, ts_pr) x y))).
          etrans.
          1: apply postcompWithBinProductArrow.
          etrans.
          2: apply pathsinv0, precompWithBinProductArrow.

          use BinProductArrowUnique.
          -- etrans.
             1: apply BinProductPr1Commutes.
             etrans.
             1: apply precompWithCoproductArrow.
             etrans.
             2: apply pathsinv0, precompWithCoproductArrow.
             use CoproductArrowUnique.
             intro.
             etrans.
             1: apply (CoproductInCommutes _ _ _ (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, BP x y))).

             etrans.
             1: apply maponpaths, id_left.
             unfold BinProductOfArrows.
             etrans.
             2: apply assoc'.
             apply maponpaths_2.
             etrans.
             2: apply pathsinv0, (BinProductPr1Commutes _ _ _ ((make_BinProduct C x y p p1 p2 p_prod))).
             apply pathsinv0, id_right.
          -- etrans.
             1: apply BinProductPr2Commutes.
             etrans.
             1: apply precompWithCoproductArrow.
             etrans.
             2: apply pathsinv0, precompWithCoproductArrow.
             use CoproductArrowUnique.
             intro.
             etrans.
             1: apply (CoproductInCommutes _ _ _ (CC (t = F) (isasetaprop (pr2 ((t = F),, ts_pr))) (λ _ : t = F, BP x y))).

             etrans.
             1: apply maponpaths, id_left.
             unfold BinProductOfArrows.
             etrans.
             2: apply assoc'.
             apply maponpaths_2.
             etrans.
             2: apply pathsinv0, (BinProductPr2Commutes _ _ _ ((make_BinProduct C x y p p1 p2 p_prod))).
             apply pathsinv0, id_right.
    - split.
      + etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply precompWithCoproductArrow.
        }

        transparent assert (i : (is_z_isomorphism (BinProductOfArrows C
    (BP (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, y)))
    (BP (CC (t = F) (Hsort t F) (λ _ : t = F, x)) (CC (t = F) (Hsort t F) (λ _ : t = F, y)))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, x)) (λ _ : t = F, identity x))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, y))
                       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, y)) (λ _ : t = F, identity y))))).
        {
          use BinProductOfArrows_is_z_iso ; (use CoproductOfArrowsIsos ; intro ; apply identity_is_z_iso).
        }

        apply pathsinv0.
        etrans.
        2: apply assoc.
        use (z_iso_inv_to_left _ _ _ (_,,i)).
        etrans.
        1: apply BinProductPr1Commutes.
        use (z_iso_inv_to_left _ _ _ (z_iso_inv (_,,(c ((t = F),, ts_pr) x y)))).
        etrans.
        1: apply assoc.
        etrans.
        1: apply maponpaths_2, BinProductPr1Commutes.

        use CoproductArrowUnique.
        intro.
        etrans.
        1: apply assoc.
        etrans.
        1: {
          apply maponpaths_2.
          apply (CoproductInCommutes _ _ _ ((CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, BP x y)))).
        }
        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply (CoproductInCommutes _ _ _ (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, x))).
        }
        etrans.
        2: apply assoc'.
        etrans.
        2: {
          apply maponpaths_2, pathsinv0.
          apply (BinProductPr1Commutes _ _ _  (make_BinProduct C x y p p1 p2 p_prod)).
        }
        apply assoc.
      + etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply precompWithCoproductArrow.
        }

        transparent assert (i : (is_z_isomorphism (BinProductOfArrows C
    (BP (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, y)))
    (BP (CC (t = F) (Hsort t F) (λ _ : t = F, x)) (CC (t = F) (Hsort t F) (λ _ : t = F, y)))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, x))
       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, x)) (λ _ : t = F, identity x))
    (CoproductOfArrows (t = F) C (CC (t = F) (Hsort t F) (λ _ : t = F, y))
                       (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, y)) (λ _ : t = F, identity y))))).
        {
          use BinProductOfArrows_is_z_iso ; (use CoproductOfArrowsIsos ; intro ; apply identity_is_z_iso).
        }

        apply pathsinv0.
        etrans.
        2: apply assoc.
        use (z_iso_inv_to_left _ _ _ (_,,i)).
        etrans.
        1: apply BinProductPr2Commutes.
        use (z_iso_inv_to_left _ _ _ (z_iso_inv (_,,(c ((t = F),, ts_pr) x y)))).
        etrans.
        1: apply assoc.
        etrans.
        1: apply maponpaths_2, BinProductPr2Commutes.

        use CoproductArrowUnique.
        intro.
        etrans.
        1: apply assoc.
        etrans.
        1: {
          apply maponpaths_2.
          apply (CoproductInCommutes _ _ _ ((CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, BP x y)))).
        }
        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply (CoproductInCommutes _ _ _ (CC (t = F) (isasetaprop ts_pr) (λ _ : t = F, y))).
        }
        etrans.
        2: apply assoc'.
        etrans.
        2: {
          apply maponpaths_2, pathsinv0.
          apply (BinProductPr2Commutes _ _ _  (make_BinProduct C x y p p1 p2 p_prod)).
        }
        apply assoc.
  Defined.

  Definition hat_exp_functor_list'_test
             (xst : list (list sort × sort) × sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (hat_exp_functor_list0 xst)
                (hat_exp_functor_list'0 xst).
  Proof.
    induction xst as [a t] ; revert a.
    use list_ind.
    - use tpair.
      + apply (nat_trans_id (C := sortToC2) (C' := sortToC2)).
      + intro ; apply (identity_is_z_iso (C := sortToC2)).
    - intros x xs IHn.

      use nat_z_iso_comp.
      3: {
        use nat_z_iso_BinProduct_of_functors.
        3: exact IHn.
        2: exact (hat_exp_functor_list'_piece_test (x ,, t)).
      }
      clear IHn.

      transparent assert (q : (nat_z_iso (exp_functor_list sort Hsort C TC BP BC CC (cons x xs)) (BinProduct_of_functors BPsortToCC (exp_functor_list sort Hsort C TC BP BC CC xs) (exp_functor sort Hsort C TC BC CC x)))).
      {
        induction xs as [[|n] xs].
        - induction xs. unfold exp_functor_list at 1. change (cons x (0,, tt)) with (cons x nil). rewrite foldr1_map_cons_nil.
          unfold exp_functor_list at 1. change (0,, tt) with (nil(A:=list sort × sort)). rewrite foldr1_map_nil.
          apply nat_z_iso_inv.
          exact (terminal_BinProduct_of_functors_unit_l _ _ BPsortToCC TsortToCC (exp_functor sort Hsort C TC BC CC x)).
        - induction xs.
          change (cons x (S n,, pr1,, pr2)) with  (cons x (cons pr1 (n,,pr2))).
          unfold exp_functor_list at 1.
          rewrite foldr1_map_cons.
          change (nat_z_iso (BinProduct_of_functors BPsortToCC (exp_functor sort Hsort C TC BC CC x) (exp_functor_list sort Hsort C TC BP BC CC (S n,, pr1,, pr2)) ) (BinProduct_of_functors BPsortToCC (exp_functor_list sort Hsort C TC BP BC CC (S n,, pr1,, pr2)) (exp_functor sort Hsort C TC BC CC x))).
          apply BinProduct_of_functors_commutes.
      }

      use (nat_z_iso_comp (post_whisker_nat_z_iso q _)).

      apply BinProduct_of_functors_distr.
      apply post_comp_functor_preserves_binproduct.
      + apply BP.
      + apply (BinProducts_functor_precat _ C BP).
      + apply hat_functor_preserves_binproducts.
        exact c.
  Defined.  (* the result will not be needed in the sequel *)


  Definition hat_exp_functor_list'_optimized_test
             (xst : list (list sort × sort) × sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (hat_exp_functor_list0 xst)
                (hat_exp_functor_list'_optimized0 xst).
  Proof.
    induction xst as [xs t]; revert t.
    induction xs as [[|n] xs].
    - induction xs.
      intro t.
      use tpair.
      + apply (nat_trans_id (C := sortToC2) (C' := sortToC2)).
      + intro ; apply (identity_is_z_iso (C := sortToC2)).
    - induction n as [|n IH].
      + induction xs as [m []].
        change (1,, m,, tt) with (cons m nil).
        intro t.
        unfold hat_exp_functor_list'_optimized0, hat_exp_functor_list'_optimized.
        rewrite foldr1_map_cons_nil.
        (* unfold hat_exp_functor_list0, hat_exp_functor_list. *)
        exact (hat_exp_functor_list'_piece_test (m,,t)).
      + induction xs as [m [k xs]].
        intro t.
        assert (IHinst := IH (k,,xs) t).
        change (S (S n),, m,, k,, xs) with (cons m (cons k (n,,xs))).
        unfold hat_exp_functor_list'_optimized0, hat_exp_functor_list'_optimized.
        rewrite foldr1_map_cons.
        change (S n,, k,, xs) with (cons k (n,,xs)) in IHinst.
        unfold hat_exp_functor_list'_optimized0, hat_exp_functor_list'_optimized in IHinst.
        use nat_z_iso_comp.
        3: {
          use nat_z_iso_BinProduct_of_functors.
          4: exact IHinst.
          2: exact (hat_exp_functor_list'_piece_test (m ,, t)).
        }
        clear IH IHinst.
        unfold hat_exp_functor_list0, hat_exp_functor_list.
        unfold exp_functor_list.
        change (pr1 (cons m (cons k (n,, xs)),, t)) with (cons m (cons k (n,, xs))).
        rewrite foldr1_map_cons.
        apply BinProduct_of_functors_distr.
        apply post_comp_functor_preserves_binproduct.
        * apply BP.
        * apply (BinProducts_functor_precat _ C BP).
        * apply hat_functor_preserves_binproducts.
          exact c.
  Defined.

  Definition MultiSortedSigToFunctor_test
             (M : MultiSortedSig sort)
             (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M)
                (MultiSortedSigToFunctor' sort Hsort C TC BP BC CC M).
  Proof.
    use coproduct_of_functors_nat_z_iso.
    intro i.
    apply hat_exp_functor_list'_optimized_test.
    exact c.
  Defined.

End EquivalenceBetweenDifferentCharacterizationsOfMultiSortedSignatureToFunctor.

(** The functor obtained from a multisorted binding signature is omega-continuous *)
Lemma is_omega_cont_MultiSortedSigToFunctor
      (sort : UU) (Hsort_set : isaset sort) (C : category)
      (TC : Terminal C) (IC : Initial C)
      (BP : BinProducts C) (BC : BinCoproducts C)
      (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C)
      (M : MultiSortedSig sort)
      (l : Lims_of_shape conat_graph C)
      (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
      (d : ∏ I : SET, ω_limits_distribute_over_I_coproducts C I l (CC (pr1 I) (pr2 I)))
  : is_omega_cont (MultiSortedSigToFunctor sort (hlevelntosn 2 _ Hsort_set) C TC BP BC CC M).
Proof.
  use nat_z_iso_preserve_ωlimits.
  3: apply (nat_z_iso_inv (MultiSortedSigToFunctor_test _ _ _ _ _ _ CC _ c)).
  apply (is_omega_cont_MultiSortedSigToFunctor' sort (hlevelntosn 2 _ Hsort_set) C TC BP BC CC _ d M).
Defined.
