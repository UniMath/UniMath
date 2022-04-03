(* In this file we construct the category of monoidal categories as the total category
   of a displayed category of the category of categories.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Require Import UniMath.Bicategories.Core.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section TensorLayer.

  Import BifunctorNotations.

  Definition tensor (C : univalent_category) : UU :=
  bifunctor C C C.
  Identity Coercion tensorintobifunctor : tensor >-> bifunctor.

  Definition preserves_tensor_data {C D : univalent_category} (TC : tensor C) (TD : tensor D) (F : functor C D) : UU :=
    ∏ (x y : C), D ⟦ F x ⊗_{TD} F y, F (x ⊗_{TC} y) ⟧.

  Definition preserves_tensor_nat {C D : univalent_category} {TC : tensor C} {TD : tensor D} {F : functor C D} (ptF : preserves_tensor_data TC TD F) : UU
    := ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      (ptF x1 y1) · (functor_on_morphisms F  (f ⊗^{TC} g)) = ((functor_on_morphisms F f) ⊗^{TD} (functor_on_morphisms F g)) · ptF x2 y2.

  Definition preserves_tensor  {C D : univalent_category} (TC : tensor C) (TD : tensor D) (F : functor C D) : UU
    := ∑ (ptF : preserves_tensor_data TC TD F), preserves_tensor_nat ptF.

  Definition preservestensor_into_preservestensordata {C D : univalent_category} {TC : tensor C} {TD : tensor D} {F : functor C D} (pt : preserves_tensor TC TD F)
    : preserves_tensor_data TC TD F := pr1 pt.
  Coercion preservestensor_into_preservestensordata : preserves_tensor >-> preserves_tensor_data.

  Definition catcatstensor_disp_ob_mor : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    use tpair.
    - exact (λ C, tensor C).
    - exact (λ C D TC TD F, preserves_tensor TC TD F).
  Defined.

  Lemma identityfunctor_preserves_tensor_data {C : univalent_category} (T : tensor C)
    : preserves_tensor_data T T (functor_identity C).
  Proof.
    intros x y.
    apply identity.
  Defined.

  Lemma identityfunctor_preserves_tensor_nat {C : univalent_category} (T : tensor C)
    : preserves_tensor_nat (identityfunctor_preserves_tensor_data T).
  Proof.
    intros x1 x2 y1 y2 f g.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition identityfunctor_preserves_tensor {C : univalent_category} (T : tensor C)
    : preserves_tensor T T (functor_identity C)
    := (identityfunctor_preserves_tensor_data T,, identityfunctor_preserves_tensor_nat T).

  Lemma compositions_preserves_tensor_data
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor_data TC TD F) (ptG : preserves_tensor_data TD TE G)
    : preserves_tensor_data TC TE (functor_composite F G).
  Proof.
    intros x y.
    exact ((ptG (F x) (F y)) · (functor_on_morphisms G) (ptF x y)).
  Defined.

  Lemma compositions_preserves_tensor_nat
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor_nat (compositions_preserves_tensor_data ptF ptG).
  Proof.
    intros x1 x2 y1 y2 f g.
    unfold compositions_preserves_tensor_data.
    simpl.
    rewrite assoc'.
    etrans. {
      apply cancel_precomposition.
      apply (pathsinv0 (functor_comp G _ _)).
    }
    rewrite (pr2 ptF).
    rewrite assoc.
    rewrite functor_comp.
    rewrite assoc.
    rewrite (pr2 ptG).
    apply idpath.
  Qed.

  Definition compositions_preserves_tensor
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor TC TE (functor_composite F G)
    := (compositions_preserves_tensor_data ptF ptG,, compositions_preserves_tensor_nat ptF ptG).

  Definition catcatstensor_disp_id_comp : disp_cat_id_comp bicat_of_univ_cats catcatstensor_disp_ob_mor.
  Proof.
    use tpair.
    - intros C TC.
      apply identityfunctor_preserves_tensor.
    - intros C D E F G TC TD TE.
      apply compositions_preserves_tensor.
  Defined.

  Definition catcatstensor_disp_catdata : disp_cat_data bicat_of_univ_cats
    := (catcatstensor_disp_ob_mor,,catcatstensor_disp_id_comp).

  Definition preservestensor_commutes
             {C D : univalent_category}
             {TC : tensor C}
             {TD : tensor D}
             {F G : functor C D}
             (ptF : preserves_tensor_data TC TD F)
             (ptG : preserves_tensor_data TC TD G)
             (α : nat_trans F G)
    : UU := ∏ (x y : C),
    (ptF x y) ·  α (x ⊗_{TC} y)
    = (α x) ⊗^{TD} (α y) · (ptG x y).

  Definition identitynattrans_preservestensor_commutes
             {C D : univalent_category}
             {TC : tensor C}
             {TD : tensor D}
             {F : functor C D}
             (ptF : preserves_tensor_data TC TD F)
    : preservestensor_commutes ptF ptF (nat_trans_id F).
  Proof.
    intros x y.
    simpl.
    rewrite id_right.
    rewrite bifunctor_distributes_over_id.
    - rewrite id_left.
      apply idpath.
    - apply bifunctor_leftid.
    - apply bifunctor_rightid.
  Qed.

  Definition bicatcatstensor_disp_2cell_struct : disp_2cell_struct catcatstensor_disp_ob_mor.
  Proof.
    intros C D F G α TC TD.
    exact (λ ptF ptG, preservestensor_commutes (pr1 ptF) (pr1 ptG) α).
  Defined.

  Lemma isaprop_bicatcatstensor_disp_2cell_struct
        {C D : bicat_of_univ_cats}
        {F G : bicat_of_univ_cats ⟦C,D⟧ }
        {α : prebicat_cells bicat_of_univ_cats F G}
        {TC : catcatstensor_disp_catdata C}
        {TD : catcatstensor_disp_catdata D}
        (ptF : TC -->[ F] TD)
        (ptG : TC -->[ G] TD)
    : isaprop (bicatcatstensor_disp_2cell_struct C D F G α TC TD ptF ptG).
  Proof.
    (* apply univalent_category_has_homsets.
  Qed. *)
  Admitted.


  Definition bicatcatstensor_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_univ_cats
    := (catcatstensor_disp_catdata,, bicatcatstensor_disp_2cell_struct).

  Definition bicatcatstensor_disp_prebicat_ops : disp_prebicat_ops bicatcatstensor_disp_prebicat_1_id_comp_cells.
  Proof.
    use tpair.
    - intros C D F TC TD ptF.
      intros x y.
      etrans. { apply id_right. }
      simpl.
      rewrite bifunctor_distributes_over_id.

      + rewrite id_left.
        apply idpath.
      + apply bifunctor_leftid.
      + apply bifunctor_rightid.
    - use tpair.
      + intros C D F TC TD ptF.
        intros x y.
        rewrite id_right.
        simpl.
        rewrite bifunctor_distributes_over_id.
        *  rewrite id_left.
           cbn.
           unfold identityfunctor_preserves_tensor_data.
           unfold compositions_preserves_tensor_data.
           rewrite functor_id.
           apply id_right.
        * apply bifunctor_leftid.
        * apply bifunctor_rightid.
      + use tpair.
        * intros C D F TC TD ptF.
          intros x y.
          rewrite id_right.
          cbn.
          unfold compositions_preserves_tensor_data.
          unfold identityfunctor_preserves_tensor_data.
          rewrite id_left.
          simpl.
          rewrite bifunctor_distributes_over_id.
          -- rewrite id_left.
             apply idpath.
          -- apply bifunctor_leftid.
          -- apply bifunctor_rightid.
        * use tpair.
          --  intros C D F TC TD ptF.
              intros x y.
              rewrite id_right.
              simpl.
              rewrite bifunctor_distributes_over_id.
              ++  rewrite id_left.
                  cbn.
                  unfold compositions_preserves_tensor_data.
                  cbn.
                  unfold identityfunctor_preserves_tensor_data.
                  rewrite functor_id.
                  rewrite id_right.
                  apply idpath.
              ++ apply bifunctor_leftid.
              ++ apply bifunctor_rightid.
          -- use tpair.
             ++ intros C D F TC TD ptF.
                intros x y.
                rewrite id_right.
                cbn.
                rewrite bifunctor_distributes_over_id.
                ** unfold compositions_preserves_tensor_data.
                   unfold identityfunctor_preserves_tensor_data.
                   simpl.
                   rewrite id_left.
                   rewrite id_left.
                   apply idpath.
                ** apply bifunctor_leftid.
                ** apply bifunctor_rightid.
             ++ use tpair.
                ** intros C D E W F G H TC TD TE TW ptF ptG ptH.
                   intros x y.
                   simpl.
                   rewrite id_right.
                   rewrite bifunctor_distributes_over_id.
                   --- rewrite id_left.
                       cbn.
                       unfold compositions_preserves_tensor_data.
                       cbn.
                       rewrite assoc'.
                       rewrite functor_comp.
                       apply idpath.
                   --- apply bifunctor_leftid.
                   --- apply bifunctor_rightid.
                ** use tpair.
                   --- intros C D E W F G H TC TD TE TW ptF ptG ptH.
                       intros x y.
                       simpl.
                       rewrite id_right.
                       rewrite bifunctor_distributes_over_id.
                       +++ rewrite id_left.
                           cbn.
                           unfold compositions_preserves_tensor_data.
                           cbn.
                           rewrite assoc'.
                           rewrite functor_comp.
                           apply idpath.
                       +++ apply bifunctor_leftid.
                       +++ apply bifunctor_rightid.
                   --- use tpair.
                       +++ intros C D F G H α β TC TD ptF ptG ptH ptcα ptcβ.
                           intros x y.
                               simpl.
                               rewrite assoc.
                               rewrite ptcα.
                               rewrite assoc'.
                               rewrite ptcβ.
                               rewrite assoc.
                               rewrite bifunctor_distributes_over_comp.
                               ---- apply idpath.
                               ---- apply bifunctor_leftcomp.
                               ---- apply bifunctor_rightcomp.
                               ---- apply bifunctor_equalwhiskers.
                       +++ use tpair.
                           *** intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
                               intros x y.
                               cbn.
                               unfold compositions_preserves_tensor_data.
                               rewrite assoc'.
                               rewrite (pr2 α).
                               rewrite assoc.
                               rewrite ptcα.
                               rewrite assoc.
                               apply idpath.
                           *** intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
                               intros x y.
                               cbn.
                               unfold compositions_preserves_tensor_data.
                               rewrite assoc'.
                               etrans. {
                                 apply cancel_precomposition.
                                 apply (pathsinv0 (functor_comp _ _ _)).
                               }
                               etrans. {
                                 apply cancel_precomposition.
                                 apply maponpaths.
                                 apply ptcα.
                               }
                               rewrite assoc.
                               rewrite functor_comp.
                               rewrite assoc.
                               apply cancel_postcomposition.

                               (* Check ((pr2 ptH) (pr1 F x) (pr1 F y) (pr1 G x) (pr1 G y) (pr1 α x) (α y)). *)

                               admit.
  Admitted.

  Definition bicatcatstensor_disp_prebicat_data : disp_prebicat_data bicat_of_univ_cats
    := (bicatcatstensor_disp_prebicat_1_id_comp_cells,, bicatcatstensor_disp_prebicat_ops).

  Definition bicatcatstensor_disp_prebicat_laws : disp_prebicat_laws bicatcatstensor_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bicatcatstensor_disp_2cell_struct.
  Qed.

  Definition bicatcatstensor_disp_prebicat : disp_prebicat bicat_of_univ_cats
    := (bicatcatstensor_disp_prebicat_data,,bicatcatstensor_disp_prebicat_laws).

  Definition bicatcatstensor_disp_bicat : disp_bicat bicat_of_univ_cats.
  Proof.
    refine (bicatcatstensor_disp_prebicat,, _).
    intros C D F G α TC TD ptF ptG.
    apply isasetaprop.
    (*apply univalent_category_has_homsets.
  Defined.*)
    Admitted.

  Theorem bicatcatstensor_disp_bicat_is_locally_univalent :
    disp_univalent_2_0 bicatcatstensor_disp_bicat.
  Proof.
  Admitted.

  Theorem bicatcatstensor_disp_bicat_is_globally_univalent :
    disp_univalent_2_1 bicatcatstensor_disp_bicat.
  Proof.
  Admitted.

  Corollary bicatcatstensor_disp_bicat_is_univalent :
    disp_univalent_2 bicatcatstensor_disp_bicat.
  Proof.
    exists bicatcatstensor_disp_bicat_is_locally_univalent.
    apply bicatcatstensor_disp_bicat_is_globally_univalent.
  Defined.

  (** ---------------------------------------------- **)
  (* Unit *)
  Definition catcatsunit_disp_ob_mor : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    use tpair.
    - exact (λ C, ob (C : univalent_category)).
    - exact (λ C D IC ID F, (D : univalent_category)⟦ID, (pr1 F) IC⟧).
  Defined.

  Definition catcatsunit_disp_cat_data : disp_cat_data bicat_of_univ_cats.
  Proof.
    use tpair.
    - exact catcatsunit_disp_ob_mor.
    - use tpair.
      + intros C I.
        exact (identity I).
      + intros C D E F G IC ID IE puF puG.
        exact (puG · (functor_on_morphisms (pr1 G) puF)).
  Defined.

  Definition bicatcatsunit_disp_2cell_struct : disp_2cell_struct catcatsunit_disp_cat_data.
  Proof.
    intros C D F G α IC ID puF puG.
    cbn in *.
    exact (puF · (α IC) = puG).
  Defined.

  Lemma isaprop_bicatcatsunit_disp_2cell_struct
        {C D : bicat_of_univ_cats}
        {F G : bicat_of_univ_cats ⟦C,D⟧ }
        {α : prebicat_cells bicat_of_univ_cats F G}
        {IC : catcatsunit_disp_cat_data C}
        {ID : catcatsunit_disp_cat_data D}
        (puF : IC -->[ F] ID)
        (puG : IC -->[ G] ID)
    : isaprop (bicatcatsunit_disp_2cell_struct C D F G α IC ID puF puG).
  Proof.
    apply univalent_category_has_homsets.
  Qed.

  Definition bicatcatsunit_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells bicat_of_univ_cats
    := (catcatsunit_disp_cat_data,, bicatcatsunit_disp_2cell_struct).

  Definition bicatcatsunit_disp_prebicat_ops : disp_prebicat_ops bicatcatsunit_disp_prebicat_1_id_comp_cells.
  Proof.
    cbn in *.
    use tpair.
    - intros C D F IC ID puF.
      apply id_right.
    - use tpair.
      + intros C D F IC ID puF.
        etrans. { apply id_right. }
        etrans. {
          apply cancel_precomposition.
          apply functor_id.
        }
        apply id_right.
      + use tpair.
        * intros C D F IC ID puF.
          etrans. { apply id_right. }
          apply id_left.
        * use tpair.
          -- intros C D F IC ID puF.
             apply cancel_precomposition.
             apply pathsinv0.
             apply functor_id.
          -- use tpair.
             ++ intros C D F IC ID puF.
                etrans. { apply id_right. }
                apply pathsinv0.
                apply id_left.
             ++ use tpair.
                ** intros C D E W F G H IC ID IE IW puF puG puH.
                   cbn.
                   unfold bicatcatsunit_disp_2cell_struct.
                   cbn.
                   etrans. { apply id_right. }
                   etrans. {
                     apply cancel_precomposition.
                     apply functor_comp.
                   }
                   etrans. { apply assoc. }
                   apply idpath.
                ** use tpair.
                   --- intros C D E W F G H IC ID IE IW puF puG puH.
                       cbn.
                       unfold bicatcatsunit_disp_2cell_struct.
                       cbn.
                       etrans.  { apply id_right. }
                       etrans. { apply assoc'. }
                       apply cancel_precomposition.
                       apply pathsinv0.
                       apply functor_comp.
                   --- use tpair.
                       +++ intros C D F G H α β IC ID puF puG puH pucα pucβ.
                           etrans. { apply assoc. }
                           etrans. {
                             apply cancel_postcomposition.
                             apply pucα.
                           }
                           apply pucβ.
                       +++ use tpair.
                           *** intros C D E F G H α IC ID IE puF puG puH pucα.
                               cbn.
                               unfold bicatcatsunit_disp_2cell_struct.
                               cbn.
                               cbn.
                               etrans. { apply assoc'. }
                               etrans. {
                                 apply cancel_precomposition.
                                 apply (pr2 α).
                               }
                               etrans. { apply assoc. }
                               apply cancel_postcomposition.
                               apply pucα.
                           *** cbn in *.
                               intros C D E F G H α IC ID IE puF puG puH pucα.
                               cbn.
                               unfold bicatcatsunit_disp_2cell_struct.
                               cbn.
                               cbn.
                               etrans. { apply assoc'. }
                               etrans. {
                                 apply cancel_precomposition.
                                 apply (pathsinv0 (functor_comp _ _ _)).
                               }
                               apply cancel_precomposition.
                               apply maponpaths.
                               apply pucα.
  Qed.

  Definition bicatcatsunit_disp_prebicat_data : disp_prebicat_data bicat_of_univ_cats
    := (bicatcatsunit_disp_prebicat_1_id_comp_cells,, bicatcatsunit_disp_prebicat_ops).

  Definition bicatcatsunit_disp_prebicat_laws : disp_prebicat_laws bicatcatsunit_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bicatcatsunit_disp_2cell_struct.
  Qed.

  Definition bicatcatsunit_disp_prebicat : disp_prebicat bicat_of_univ_cats
    := (bicatcatsunit_disp_prebicat_data,,bicatcatsunit_disp_prebicat_laws).

  Definition bicatcatsunit_disp_bicat : disp_bicat bicat_of_univ_cats.
  Proof.
    refine (bicatcatsunit_disp_prebicat,, _).
    intros C D F G α IC ID puF puG.
    apply isasetaprop.
    apply univalent_category_has_homsets.
  Defined.

  Lemma bicatcatsunit_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bicatcatsunit_disp_bicat.
  Proof.
    intros C D F G pfFisG IC ID puF puG.
    induction pfFisG.
    apply isweqimplimpl.
    - cbn.
      intros α.
      pose (pr1 α) as d.
      cbn in *.
      unfold bicatcatsunit_disp_2cell_struct in *.
      rewrite id_right in d.
      exact d.
    - apply univalent_category_has_homsets.
    - apply invproofirrelevance.
      intro ; intro.
      use subtypePath.
      + intro x0.
        apply isaprop_is_disp_invertible_2cell.
      + apply univalent_category_has_homsets.
  Qed.

  Lemma bicatcatsunit_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatsunit_disp_bicat.
  Proof.
    unfold disp_univalent_2_0.
    intros C D pfCisD IC ID.
    induction pfCisD.

    use weqhomot.
    - use make_weq.
      + intro equalunits.
        induction equalunits.
        apply disp_identity_adjoint_equivalence.
      + use isweq_iso.
        * intro equalunits.
          induction equalunits as [adj_inv adj_prop].
          cbn.
          apply C.
          Search (Isos.iso _).
          apply Isos.z_iso_to_iso.
          use tpair.
          -- cbn in *.
             apply adj_prop.
          -- cbn in *.
             use tpair.
             ++ apply adj_inv.
             ++ use tpair.
                ** induction adj_prop.
                   induction pr1.
                   induction pr0.
                   cbn in *.
                   unfold nat_trans_id in pr0.
                   cbn in pr0.
                   unfold functor_identity in pr0.
                   Check pr0.
                   (* unfold bicatcatsunit_disp_2cell_struct in pr0. *)
                   etrans. {
                     apply (pathsinv0 pr0).
                   }
                   apply id_left.
                ** cbn.
                  induction adj_prop.
                   induction pr1.
                   induction pr0.
                   cbn in *.
                   (* unfold nat_trans_id in pr3. *)
                   cbn in pr3.
                   unfold bicatcatsunit_disp_2cell_struct in pr3.
                   unfold functor_identity in pr3.
                   cbn in pr3.
                   apply pathsinv0.
                   etrans. {
                     apply (pathsinv0 pr3).
                   }
                   apply id_right.
        * cbn.
          intro equalunits.
          induction equalunits.
          cbn.
          admit.
        * cbn.
          intro adj.
          induction adj as [adj_inv adj_prop].
          (* use total2_paths_b.
          -- cbn. *)
          admit.

    - intro equalunits.
      induction equalunits.
      apply idpath.
  Admitted. (* Qed. *)
