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

    use make_isBinProduct.
    intros Q Q1 Q2.
    use tpair.
    - use tpair.
      + use make_nat_trans.
        * intro c.
          cbn.
          set (Q1c := pr1 Q1 c) ; cbn in Q1c.
          set (Q2c := pr1 Q2 c) ; cbn in Q2c.

          transparent assert (FPp : (BinProduct D (pr1 F1 c) (pr1 F2 c))).
          { apply BPD. }

          transparent assert (HFp : (BinProduct E (F (pr1 F1 c)) (F (pr1 F2 c)))).
          { exact (make_BinProduct _ _ _ _ _ _ (Fp (pr1 F1 c) (pr1 F2 c) _ _ _ (pr2 FPp))). }

          transparent assert (HFp' : (BinProduct E (F (pr1 F1 c)) (F (pr1 F2 c)))).
          { apply BPE. }

          refine (pr11 (pr2 HFp _ Q1c Q2c) · _).
          apply (#F).

          (* refine (iso_between_BinProduct _ FPp). Something like this. *)

  Admitted.

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
  (* Need lemma: is_z_isomorphism_BinProductOfArrows
       whi       ch states that the BinProductOfArrows of isomorphisms is again an isomorphism *)
  Admitted.

End A.

Section EquivalenceBetweenDifferentCharacterizationsOfMultiSortedSignatureToFunctor.

  Variables (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).
  Variables (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

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
             (Hsort_set : isaset sort)
             (c : propcoproducts_commute_binproducts C BP (λ p, CC p (isasetaprop (pr2 p))))
    : preserves_binproduct (hat_functor sort Hsort C CC t).
  Proof.
    intros x y p p1 p2 p_prod.
    use make_isBinProduct.
    - intros F F1 F2.
      use tpair.
      + use tpair.
        * use make_nat_trans.
          -- intro s.
             set (F1s := pr1 F1 s) ; cbn in F1s.
             set (F2s := pr1 F2 s) ; cbn in F2s.

             set (BPxy := BP
                            (CoproductObject (t = s) C (CC (t = s) (Hsort t s) (λ _ : t = s, x)))
                            (CoproductObject (t = s) C (CC (t = s) (Hsort t s) (λ _ : t = s, y)))).

             set (h := pr2 BPxy (pr1 F s) F1s F2s).
             refine (pr11 h · _).

             assert (ts_pr : isaprop (t = s)).
             { apply Hsort_set. }

             refine (_ · pr1 (c (_,,ts_pr) x y) · _).
             ++ use BinProductOfArrows ; use CoproductOfArrows ; intro ; apply identity.
             ++ use CoproductOfArrows.
                intro i.
                exact (BinProductOfArrows _ (make_BinProduct _ _ _ _ _ _ p_prod) (BP x y) (identity _) (identity _)).
          -- intros s1 s2 f.
             cbn.




  Admitted.

  Definition hat_exp_functor_list'_test
             (xst : list (list sort × sort) × sort)
             (Hsort_set : isaset sort)
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
        * exact Hsort_set.
        * exact c.
  Admitted.

  Definition MultiSortedSigToFunctor_test
             (M : MultiSortedSig sort)
             (Hsort_set : isaset sort)
             (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
    : nat_z_iso (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M)
                (MultiSortedSigToFunctor' sort Hsort C TC BP BC CC M).
  Proof.
    use coproduct_of_functors_nat_z_iso.
    intro i.
    apply hat_exp_functor_list'_test.
    - exact Hsort_set.
    - exact c.
  Defined.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort)
        (Hsort_set : isaset sort)
        (l : ∏ coch : cochain C, LimCone coch)
        (c : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
        (d : ∏ I : SET, ω_limits_distribute_over_I_coproducts C I l (CC (pr1 I) (pr2 I)))
    : is_omega_cont (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M).
  Proof.
    use nat_z_iso_preserve_ωlimits.
    3: exact (nat_z_iso_inv (MultiSortedSigToFunctor_test M Hsort_set c)).
    apply (is_omega_cont_MultiSortedSigToFunctor' sort Hsort C TC BP BC CC _ d M).
  Defined.

End EquivalenceBetweenDifferentCharacterizationsOfMultiSortedSignatureToFunctor.
