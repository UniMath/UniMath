Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

Require Import UniMath.CategoryTheory.limits.Preservation.

Local Open Scope cat.

Section B.

  Lemma make_isBinProduct'
        {C : category} {x y : C}
        (Pxy : BinProduct _ x y)
    : ∏ z : C, ∏ (zx : C⟦z,x⟧) (zy : C⟦z,y⟧),
        (∑ i : is_z_isomorphism (BinProductArrow C Pxy zx zy),
            pr1 i · zx = BinProductPr1 _ Pxy × pr1 i · zy = BinProductPr2 _ Pxy)
          -> isBinProduct C x y z zx zy.
  Proof.
    intros z zx zy [i [px py]].
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
             (CP : Coproducts I C)
    : ∏ x y : C, C⟦CP (λ p : I, BP x y), BP (CP (λ p : I, x)) (CP (λ p : I, y))⟧.
  Proof.
    intros x y.
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


  (* Definition BinProduct_functor_cat_to_codomain
     {C D : category}
     (F1 F2 : [C,D])
     (BP : BinProducts [C,D])
     : BinProducts D.
     Proof.
     intros d1 d2.
     use make_BinProduct.
     - set (cd1 := constant_functor C D d1).
     set (cd2 := constant_functor C D d2).
     set (cd := BP cd1 cd2).
     Check pr11 cd.

     Defined. *)

  Definition post_comp_functor_preserves_binproduct
             (C : category) {D E : category} (F : functor D E)
             (BPD : BinProducts D)
             (BPE  : BinProducts E)
             (Fp : preserves_binproduct F)
    : preserves_binproduct (post_comp_functor (A := C) F).
  Proof.
    intros F1 F2 P P1 P2 P_prod.

    (* By assumption of D having binary products,
       we have that P(c × d) ≅ Pc × Pd.
     *)

    use make_isBinProduct'.
    {
      apply functor_precat_binproduct_cone.
      exact BPE.
    }
    use tpair.
    - use nat_trafo_z_iso_if_pointwise_z_iso.
      intro c.
      use make_is_z_isomorphism.
      + transparent assert (FPp : (BinProduct D (pr1 F1 c) (pr1 F2 c))).
        { apply BPD. }

        transparent assert (HFp : (BinProduct E (F (pr1 F1 c)) (F (pr1 F2 c)))).
        { exact (make_BinProduct _ _ _ _ _ _ (Fp (pr1 F1 c) (pr1 F2 c) _ _ _ (pr2 FPp))). }

        transparent assert (P_p : (BinProduct D (pr1 F1 c) (pr1 F2 c))).
        {
          use make_BinProduct.
          - exact (pr1 P c).
          - exact (pr1 P1 c).
          - exact (pr1 P2 c).
          - use make_isBinProduct.
            admit.
        }

        refine (pr11 (pr2 HFp _ _ _) · _).
        { apply BinProductPr1. }
        { apply BinProductPr2. }
        apply (#F).
        * use (BinProductArrow _ P_p).
          -- apply BinProductPr1.
          -- apply BinProductPr2.
      + split.
        * cbn.
          unfold binproduct_nat_trans_data.
          cbn.
          unfold preserves_binproduct in Fp.

          etrans.
          1: apply assoc.

          transparent assert (FPp : (BinProduct D (pr1 F1 c) (pr1 F2 c))).
          { apply BPD. }

          transparent assert (HFp : (BinProduct E (F (pr1 F1 c)) (F (pr1 F2 c)))).
          { exact (make_BinProduct _ _ _ _ _ _ (Fp (pr1 F1 c) (pr1 F2 c) _ _ _ (pr2 FPp))). }


          etrans.
          1: {
            apply maponpaths_2.
            refine (_ @ idpath (#F _)).
            Search BinProductArrow.
            Check (postcompWithBinProductArrow _ HFp (BPE (F (pr1 F1 c)) (F (pr1 F2 c))) (_ · # (pr1 F) (pr1 P1 c)) (_ · # (pr1 F) (pr1 P2 c))).
            admit.
          }
          etrans.
          1: apply pathsinv0, functor_comp.

          admit.
        * admit.
    - split.
      + cbn.
        use nat_trans_eq.
        { apply homset_property. }
        intro c.
        cbn.
        unfold binproduct_nat_trans_pr1_data.
        cbn.







  Admitted.

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

  Variables (sort : UU) (Hsort_set : isaset sort) (C : category).
  Variables (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

  Let Hsort := hlevelntosn 2 _ Hsort_set.
  (** Define the discrete category of sorts *)
  Let sort_cat : category := path_pregroupoid sort Hsort.

  (** This represents "sort → C" *)
  Let sortToC : category := [sort_cat,C].
  Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

  Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
  Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

  Lemma sortToC_hasbinproducts
    : BinProducts [sortToC, sortToC].
  Proof.
    repeat (apply BinProducts_functor_precat) ; exact BP.
  Defined.

  Lemma sortToC_hascoproducts
    : ∏ I : UU, isaset I -> Coproducts I [sortToC, sortToC].
  Proof.
    intros I Iset.
    repeat (apply Coproducts_functor_precat) ; exact (CC I Iset).
  Defined.

  Let hat_exp_functor_list'_piece0
      := hat_exp_functor_list'_piece sort Hsort C TC BC CC.

  Let hat_exp_functor_list0
      := hat_exp_functor_list sort Hsort C TC BP BC CC.
  Let hat_exp_functor_list'0
      := hat_exp_functor_list' sort Hsort C TC BP BC CC.

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
    - simpl.
      (* assert (p : exp_functor sort Hsort C TC BC CC (nil,, s)
                  = (post_comp_functor (projSortToC sort Hsort C s))).
      { apply idpath. } *)
      unfold hat_exp_functor_list'_piece0.
      unfold hat_exp_functor_list'_piece.

      use make_nat_z_iso.
      + use make_nat_trans.
        * intro ; apply (nat_trans_id (C := sortToC) (C' := sortToC)).
        * intro ; intros.
          (* assert (p : nat_trans_id
      (pr1 (functor_composite (pre_comp_functor (option_list sort Hsort C TC BC CC nil))
                          (post_comp_functor (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CC t)) : functor_data [sortToC,sortToC] [sortToC,sortToC]) x' : functor sortToC sortToC)
                  = identity (C := [sortToC,sortToC]) _).
          {
            apply idpath.
          }
          etrans.
          1: {
            apply maponpaths.
            exact p.
          }
          etrans.
          1:  apply (id_right (C := [sortToC,sortToC])). *)
          admit.
          (* This should just be: exact (id_right (C := [sortToC,sortToC]) _ @ ! id_left (C := [sortToC,sortToC]) _).
           But I can't get it to type check... *)

      + intro.
        (* Search is_z_isomorphism.
        apply (identity_is_z_iso (C := [sortToC,sortToC])). *)



      admit.
    - intro ; intros.
      use nat_z_iso_inv.
      apply post_comp_functor_of_comp.
  Admitted.



  Definition hat_functor_preserves_binproducts (t : sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : preserves_binproduct (hat_functor sort Hsort C CC t).
  Proof.
    intros x y p p1 p2 p_prod.

    use make_isBinProduct'.
    { use functor_precat_binproduct_cone ; exact BP. }
    use tpair.
    - use nat_trafo_z_iso_if_pointwise_z_iso.
      intro F.
      use make_is_z_isomorphism.
      + assert (ts_pr : isaprop (t = F)).
        { apply Hsort_set. }

        refine (_ · pr1 (c (_,,ts_pr) x y) · _).
        ++ use BinProductOfArrows ; use CoproductOfArrows ; intro ; apply identity.
        ++ use CoproductOfArrows.
           intro i.
           exact (BinProductOfArrows _ (make_BinProduct _ _ _ _ _ _ p_prod) (BP x y) (identity _) (identity _)).
      + split.
        * cbn.
          unfold binproduct_nat_trans_data.
          cbn.
          Search BinProductArrow.

          etrans.
          1: apply assoc.




          (* etrans.
          1: {
            apply maponpaths_2.
            unfold propcoproducts_commute_binproducts in c.
            unfold coproducts_commute_binproducts_mor in c.
            apply maponpaths.
            unfold BinProductOfArrows.
            Check (pr12 (c ((t = F),, Hsort_set t F) x y)).

          etrans.
          1: {
            apply maponpaths_2.
            etrans.
            1: apply assoc.
            apply maponpaths_2.
            apply postcompWithBinProductArrow.
          }
          etrans.
          1: {
            apply maponpaths_2.
            unfold propcoproducts_commute_binproducts in c.
            unfold coproducts_commute_binproducts_mor in c.

            apply (pr12 (c ((t = F),, Hsort_set t F) x y)).


          Check CoproductArrowUnique _ _ _ (CC (t = F) (Hsort t F) (λ _ : t = F, p)). *)
        admit.
        *
          admit.
    - split.
      + simpl.
        use nat_trans_eq.
        { apply homset_property. }
        intro s.
        cbn.
        unfold binproduct_nat_trans_pr1_data.
        cbn.

        assert (pf : (CC (t = s) (isasetaprop (Hsort_set t s)) (λ _ : t = s, BP x y))
                     = (CC (t = s) (Hsort t s) (λ _ : t = s, BP x y))).
        {
          use (maponpaths (λ g, CC (t = s) g (λ _ : t = s, BP x y))).
          apply (isapropisaset (t = s)).
        }

        assert (pf0 : pr11 (CC (t = s) (isasetaprop (Hsort_set t s)) (λ _ : t = s, BP x y))
                     = pr11 (CC (t = s) (Hsort t s) (λ _ : t = s, BP x y))).
        {
          use (maponpaths (λ g, pr11 (CC (t = s) g (λ _ : t = s, BP x y)))).
          apply (isapropisaset (t = s)).
        }

        etrans.
        1: {
          do 3 apply maponpaths_2.
          (* this is the identity, it is just not recognized... *)

          admit.
        }

        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply precompWithCoproductArrow.
        }
        cbn.

        unfold propcoproducts_commute_binproducts in c.
        unfold coproducts_commute_binproducts_mor in c.
        (* If the above issue is solved, use that
            pr1 (c ((t = s),, Hsort_set t s) x y)
            is an inverse.
            Then we get on the righthandside BinProductArrow.
            Then, use BinProductPr1Commutes.
         *)




  Admitted.

  Definition hat_exp_functor_list'_test
             (xst : list (list sort × sort) × sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (hat_exp_functor_list0 xst)
                (hat_exp_functor_list'0 xst).
  Proof.
    induction xst as [a t] ; revert a.
    use list_ind.
    - use tpair.
      + apply (nat_trans_id (C := [sortToC,sortToC]) (C' := [sortToC,sortToC])).
      + intro ; apply (identity_is_z_iso (C := [sortToC,sortToC])).
    - intros x xs IHn.

      use nat_z_iso_comp.
      3: {
        use nat_z_iso_BinProduct_of_functors.
        3: exact IHn.
        2: exact (hat_exp_functor_list'_piece_test (x ,, t)).
      }
      clear IHn.

      transparent assert (q : (nat_z_iso (exp_functor_list sort Hsort C TC BP BC CC (cons x xs)) (BinProduct_of_functors BPC (exp_functor_list sort Hsort C TC BP BC CC xs) (exp_functor sort Hsort C TC BC CC x)))).
      {
        admit.
      }

      use (nat_z_iso_comp (post_whisker_nat_z_iso q _)).

      apply BinProduct_of_functors_distr.
      apply post_comp_functor_preserves_binproduct.
      + apply BP.
      + apply (BinProducts_functor_precat _ C BP).
      + apply hat_functor_preserves_binproducts.
        exact c.
  Admitted.

  Definition MultiSortedSigToFunctor_test
             (M : MultiSortedSig sort)
             (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M)
                (MultiSortedSigToFunctor' sort Hsort C TC BP BC CC M).
  Proof.
    use coproduct_of_functors_nat_z_iso.
    intro i.
    apply hat_exp_functor_list'_test.
    exact c.
  Defined.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort)
        (l : Lims_of_shape conat_graph C)
        (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
        (d : ∏ I : SET, ω_limits_distribute_over_I_coproducts C I l (CC (pr1 I) (pr2 I)))
    : is_omega_cont (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M).
  Proof.
    use nat_z_iso_preserve_ωlimits.
    3: exact (nat_z_iso_inv (MultiSortedSigToFunctor_test M c)).
    apply (is_omega_cont_MultiSortedSigToFunctor' sort Hsort C TC BP BC CC _ d M).
  Defined.

End EquivalenceBetweenDifferentCharacterizationsOfMultiSortedSignatureToFunctor.
