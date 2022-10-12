Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesReordered.

Section MonoidalCategoriesReordered0.

  Definition lunitor0_nattrans {C : category} (T : tensor C) (I : C) : UU
    := ∑ lu : leftunitor_data T I, leftunitor_nat lu.

  Definition lunitor0 {C : category} (T : tensor C) (I : C) : UU
    := ∑ lu : lunitor0_nattrans T I, ∑ lui : leftunitorinv_data T I, leftunitor_iso_law (pr1 lu) lui.

  Definition runitor0_nattrans {C : category} (T : tensor C) (I : C) : UU
    := ∑ ru : rightunitor_data T I, rightunitor_nat ru.
  Definition runitor0 {C : category} (T : tensor C) (I : C) : UU
    := ∑ ru : runitor0_nattrans T I, ∑ rui : rightunitorinv_data T I, rightunitor_iso_law (pr1 ru) rui.


  Definition associator0_nattrans {C : category} (T : tensor C) : UU
    := ∑ ass : associator_data T,
        associator_nat_leftwhisker ass × associator_nat_rightwhisker ass × associator_nat_leftrightwhisker ass.
  Definition associator0 {C : category} (T : tensor C) : UU
    := ∑ ass : associator0_nattrans T, ∑ assi : associatorinv_data T, associator_iso_law (pr1 ass) assi.

  Definition monstruct0 (C : category) : UU
    := ∑ T : tensor C, ∑ I : C, ∑ lu : lunitor0 T I, ∑ ru : runitor0 T I, ∑ ass : associator0 T,
                triangle_identity (pr11 lu) (pr11 ru) (pr11 ass) × pentagon_identity (pr11 ass).

  Definition moncats0 : UU := ∑ C : category, monstruct0 C.

End MonoidalCategoriesReordered0.

Section EquivalenceMonoidalCategoriesReordered0WithMonstructs.

  Definition moncats : UU := ∑ C : category, monoidal_struct C.

  Lemma moncats_equiv_moncats0
    : moncats ≃ moncats0.
  Proof.
    apply weqfibtototal.
    intro C.
    unfold monoidal_struct ; unfold monstruct0.
    use weq_iso.
    - intro M.
      exists (pr111 M).
      exists (pr211 M).
      repeat (use tpair).
      * intro x ; apply (pr1 (pr121 M) x).
      * intros x y f ; apply (pr2 (pr121 M) x y f).
      * intro x ; apply (pr1 (pr122 M) x).
      * intro x ; apply (pr2 (pr122 M) x).

      * intro x ; apply (pr11 (pr221 M) x).
      * intros x y f ; apply (pr21 (pr221 M) x y f).
      * intro x ; apply (pr11 (pr222 M) x).
      * intro x ; apply (pr21 (pr222 M) x).

      * intros x y z ; apply (pr12 (pr221 M) x y z).
      * intro ; intros ; apply (pr122 (pr221 M)).
      * intro ; intros ; apply (pr1 (pr222 (pr221 M))).
      * intro ; intros ; apply (pr2 (pr222 (pr221 M))).
      * intro ; intros ; apply ((pr12 (pr222 M))).
      * intro ; intros ; apply ((pr22 (pr222 M))).
      * intro ; intros ; apply (pr112 M).
      * intro ; intros ; apply (pr212 M).
    - intro M.
      use tpair.
      + exists (pr1 M ,, pr12 M).
        repeat split ; apply (pr22 M).
      + simpl.
        repeat split.
        * apply (pr22 (pr222 M)).
        * apply (pr22 (pr222 M)).
        * apply ((pr122 M)).
        * apply (pr1 (pr222 M)).
        * apply (pr12 (pr222 M)).
    - apply idpath.
    - apply idpath.
  Defined.

End EquivalenceMonoidalCategoriesReordered0WithMonstructs.

Section EquivalenceMonoidalCategoriesReordered0WithUncurried.

  Definition lunitors_equiv {C : category} (T : tensor C) (I : C)
    :   lunitor0 T I ≃ left_unitor (bifunctor_to_functorfromproductcat T) I.
  Proof.
    use weqtotal2.
    {
      use weqtotal2.
      - apply idweq.
      - intro lu.
        use weq_iso.

        + intro lunat.
          (* show we get natural transformation *)
          intros x y f.
          etrans. { apply maponpaths_2 ; apply when_bifunctor_becomes_leftwhiskering. }
          apply (lunat x y f).

        + intro lunattrans.
          (* show we get the naturality law of the unitor *)
          intros x y f.
          use (_ @ lunattrans x y f).
          apply maponpaths_2.
          apply (! when_bifunctor_becomes_leftwhiskering _ _ _).

        + intro.
          (* Show that (lefunitor_nat lu) is a prop. *)
          repeat (apply impred_isaprop ; intro) ; apply homset_property.

        + intro.
          apply isaprop_is_nat_trans.
          apply homset_property.
    }
    intro lunat.
    simpl.
    use (weqtotaltoforall (X := C) (λ x,  C ⟦ x, bifunctor_on_objects T I x ⟧)).
  Defined.

  Definition runitors_equiv {C : category} (T : tensor C) (I : C)
    :   runitor0 T I ≃ right_unitor (bifunctor_to_functorfromproductcat T) I.
  Proof.
    use weqtotal2.
    {
      use weqtotal2.
      - apply idweq.
      - intro lu.
        use weq_iso.

        + intro runat.
          (* show we get natural transformation *)
          intros x y f.
          etrans. { apply maponpaths_2 ; apply when_bifunctor_becomes_rightwhiskering. }
          apply (runat x y f).

        + intro runattrans.
          (* show we get the naturality law of the unitor *)
          intros x y f.
          use (_ @ runattrans x y f).
          apply maponpaths_2.
          apply (! when_bifunctor_becomes_rightwhiskering _ _ _).

        + intro.
          (* Show that (rightunitor_nat lu) is a prop. *)
          repeat (apply impred_isaprop ; intro) ; apply homset_property.

        + intro.
          apply isaprop_is_nat_trans.
          apply homset_property.
    }
    intro.
    simpl.
    use (weqtotaltoforall (X := C) (λ x,  C ⟦ x , bifunctor_on_objects T x I ⟧)).
  Defined.

  Definition associators_equiv {C : category} (T : tensor C)
    : associator0 T ≃ associator (bifunctor_to_functorfromproductcat T).
  Proof.
    use weqtotal2.
    {
      use weqtotal2.
      - use weq_iso.
        { exact (λ ass xyz, ass (pr11 xyz) (pr21 xyz) (pr2 xyz)). }
        { exact (λ nt x y z, nt ((x,,y),,z)). }
        { intro ; apply idpath. }
        intro ; apply idpath.

      - intro ass.
        use weq_iso.

        + intro assnat.
          (* show we get natural transformation *)
          do 3 intro.
          use (! associator_nat2 _ _ _ _ _ _) ; apply assnat.

        + intro assnattrans.
          (* show we get the three naturality laws of the associator *)
          repeat split.
          * intros x y z1 z2 h.
            set (t := ! assnattrans _ _ ((id x #, id y) #, h)).
            simpl in t.
            unfold functoronmorphisms1 in t.
            refine (_ @ t @ _).
            {
              etrans.
              2: { apply maponpaths ; apply maponpaths_2 ; apply when_bifunctor_becomes_rightwhiskering. }
              etrans.
              2: { apply maponpaths ; apply maponpaths_2 ; use (! bifunctor_distributes_over_id _ _ _ _) ; apply T. }
              apply maponpaths.

              etrans.
              2: { do 2 apply maponpaths ; apply maponpaths_2 ; apply when_bifunctor_becomes_rightwhiskering. }
              etrans.
              2: {
                do 2 apply maponpaths ; apply maponpaths_2 ; use (! bifunctor_distributes_over_id _ _ _ _) ; apply T. }
              etrans.
              2: { do 2 apply maponpaths ; apply (! id_left _). }
              apply  (! id_left _).
            }

            etrans.
            {
              do 2 apply maponpaths_2.
              etrans. {
                apply maponpaths.
                etrans. { apply maponpaths ; apply bifunctor_leftid. }
                etrans. { apply id_right. }
                apply bifunctor_rightid.
              }
              apply bifunctor_rightid.
            }
            etrans. { apply assoc'. }
            apply id_left.
          * intros x1 x2 y z f.
            set (t := ! assnattrans _ _ ((f #, id y) #, id z)).
            simpl in t.
            unfold functoronmorphisms1 in t.
            refine (_ @ t @ _).
            {
              etrans.
              2: { apply maponpaths ; apply maponpaths_2 ; apply when_bifunctor_becomes_rightwhiskering. }
              etrans.
              2: {
                apply maponpaths ; apply maponpaths_2.
                apply (! when_bifunctor_becomes_rightwhiskering _ _ _).
              }
              apply maponpaths.

              etrans.
              2: { do 2 apply maponpaths ; apply maponpaths_2 ; apply when_bifunctor_becomes_rightwhiskering. }
              etrans.
              2: {
                do 2 apply maponpaths ; apply maponpaths_2 ; use (! bifunctor_distributes_over_id _ _ _ _) ; apply T. }
              etrans.
              2: { do 2 apply maponpaths ; apply (! id_left _). }
              etrans.
              2: { do 2 apply maponpaths ; apply (! bifunctor_leftid _ _ _). }
              etrans.
              2: {
                apply maponpaths.
                apply (! bifunctor_leftid _ _ _).
              }
              apply  (! id_right _).
            }

            etrans.
            {
              do 2 apply maponpaths_2.
              apply maponpaths.
              etrans. { apply maponpaths ; apply bifunctor_leftid. }
              apply id_right.
            }
            etrans. {
              apply maponpaths_2 ; apply maponpaths.
              apply bifunctor_leftid.
            }

            etrans. { apply assoc'. }
            apply maponpaths.
            apply id_left.
          * intros x y1 y2 z g.
            set (t := ! assnattrans _ _ ((id x #, g) #, id z)).
            simpl in t.
            refine (_ @ t @ _).
            {
              etrans.
              2: { do 2 apply maponpaths ; apply (! when_bifunctor_becomes_rightwhiskering _ _ _). }
              apply maponpaths.
              apply (! when_bifunctor_becomes_leftwhiskering _ _ _).
            }
            etrans.
            { do 2 apply maponpaths_2 ; apply when_bifunctor_becomes_leftwhiskering. }
            apply maponpaths_2.
            apply when_bifunctor_becomes_rightwhiskering.

        + intro ; repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; apply homset_property.
        + intro. repeat (apply impred_isaprop ; intro) ; apply homset_property.
    }

    intro ass.

    refine (weqtotaltoforall (X :=  precategory_binproduct_data (precategory_binproduct_data C C) C) _ _ ∘ _)%weq.
    use weqtotal2.
    {
      use weq_iso.
      { exact (λ assinv xyz, assinv (pr11 xyz) (pr21 xyz) (pr2 xyz)). }
      { exact (λ assinv x y z, assinv ((x,,y),,z)). }
      { intro ; apply idpath. }
      { intro ; apply idpath. }
    }
    intro assinv.
    apply weqimplimpl.
    - intros isolaw xyz.
      apply isolaw.
    - intros isolaw x y z.
      apply (isolaw ((x,,y),,z)).
    - repeat (apply impred_isaprop ; intro) ; apply isaprop_is_inverse_in_precat.
    - repeat (apply impred_isaprop ; intro) ; apply isaprop_is_inverse_in_precat.
  Defined.

  Definition moncats0_equiv_uncurried
    : moncats0 ≃ MonoidalCategories.monoidal_cat.
  Proof.
    apply weqfibtototal.
    intro C.
    use weqtotal2.
    { apply bifunctor_equiv_functorfromproductcat. }
    intro T.
    use weqtotal2.
    { apply idweq. }
    intro I.
    use weqtotal2.
    { apply lunitors_equiv. }
    intro lu.
    use weqtotal2.
    { apply runitors_equiv. }
    intro ru.
    use weqtotal2.
    { apply associators_equiv. }
    intro ass.

    apply weqdirprodf ; apply weqimplimpl.
    {
      intros ti x y.
      etrans. { apply when_bifunctor_becomes_rightwhiskering. }
      etrans.
      2: { apply maponpaths ; apply (! when_bifunctor_becomes_leftwhiskering _ _ _). }
      apply (! ti x y).
    }
    {
      intros ti x y.
      refine (_ @ ! ti x y @ _).
      - apply maponpaths.
        apply (! when_bifunctor_becomes_leftwhiskering _ _ _).
      - apply when_bifunctor_becomes_rightwhiskering.
    }
    { repeat (apply impred_isaprop ; intro) ; apply homset_property. }
    { repeat (apply impred_isaprop ; intro) ; apply homset_property. }

    {
      intros pi w x y z.
      refine (! pi w x y z @ _).
      etrans.
      2: { do 2 apply maponpaths_2 ; apply (! when_bifunctor_becomes_rightwhiskering _ _ _). }
      apply maponpaths.
      apply (! when_bifunctor_becomes_leftwhiskering _ _ _).
    }
    {
      intros pi w x y z.
      refine (_ @ ! pi w x y z).
      simpl.
      etrans.
      2: { do 2 apply maponpaths_2 ; apply (! when_bifunctor_becomes_rightwhiskering _ _ _). }
      apply maponpaths.
      apply (! when_bifunctor_becomes_leftwhiskering _ _ _).
    }
    { repeat (apply impred_isaprop ; intro) ; apply homset_property. }
    repeat (apply impred_isaprop ; intro) ; apply homset_property.
  Defined.

End EquivalenceMonoidalCategoriesReordered0WithUncurried.
