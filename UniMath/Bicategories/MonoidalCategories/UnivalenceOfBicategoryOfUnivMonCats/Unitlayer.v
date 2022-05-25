(*
This is the first of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the first displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories together with a fixed object (which will be the unit for the monoidal structure).
- The morphisms are functors which preserve the unit in a lax/weak sense (i.e. a non-necessairly isomorphic morphism).
- The 2-cells are natural transformations which (at the unit) preserves the morphism of the underlying functors.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
(* Require Import UniMath.CategoryTheory.DisplayedCats.Constructions. *)

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section UnitLayer.

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
        cbn.
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

  Lemma dispadjequiv_to_iso (C : bicat_of_univ_cats) (IC ID : bicatcatsunit_disp_bicat C) :
       (disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) IC ID) -> (Isos.z_iso IC ID).
  Proof.
    intro equalunits.
    induction equalunits as [f adj].
    induction adj as [data [ladj_ax weq_ax]].
    induction data as [finv [dunit dcounit]].
    cbn in *.
    unfold functor_identity in dunit.
    unfold nat_trans_id in dunit.
    cbn in dunit.

    use tpair.
    - exact finv.
    - repeat (use tpair).
      + exact f.
      + unfold nat_trans_id in dunit.
        unfold functor_identity in dunit.
        cbn in *.
        etrans. { apply (pathsinv0 dunit). }
        apply id_left.
      + unfold nat_trans_id in dcounit.
        unfold functor_identity in dcounit.
        apply pathsinv0.
        etrans. { apply (pathsinv0 dcounit). }
        apply id_right.
  Defined.

  Lemma iso_to_dispadjequiv (C : bicat_of_univ_cats) (IC ID : bicatcatsunit_disp_bicat C) :
    (z_iso IC ID) -> (disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) IC ID).
  Proof.
    intro i.
    induction i as [finv [f [li ri]]].
    split with f.
    unfold disp_left_adjoint_equivalence.
    repeat (use tpair).
    - exact finv.
    - etrans. { apply id_left. }
      exact (! li).
    - cbn.
      unfold bicatcatsunit_disp_2cell_struct.
      etrans. {
        apply cancel_postcomposition.
        apply ri.
      }
      apply id_right.
    - apply univalent_category_has_homsets.
    - apply univalent_category_has_homsets.
    - unfold disp_2cells.
      cbn in *.
      unfold bicatcatsunit_disp_2cell_struct.
      etrans. {
        apply cancel_postcomposition.
        apply li.
      }
      apply id_left.
    - apply univalent_category_has_homsets.
    - apply univalent_category_has_homsets.
    - unfold disp_2cells.
      cbn in *.
      unfold bicatcatsunit_disp_2cell_struct.
      etrans. { apply id_left. }
      exact (! ri).
    - apply univalent_category_has_homsets.
    - apply univalent_category_has_homsets.
  Defined.

    Lemma iso_dispadjequiv_equivalence (C : bicat_of_univ_cats) (IC ID : bicatcatsunit_disp_bicat C) :
    (z_iso IC ID) ≃ (disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) IC ID).
  Proof.
    use make_weq.
    - apply iso_to_dispadjequiv.
    - use isweq_iso.
      + apply dispadjequiv_to_iso.
      + intro i.
        induction i.
        use subtypePath.
        * intro f.
          apply isaprop_is_z_isomorphism.
        * apply idpath.
      + intro adjequiv.
        unfold iso_to_dispadjequiv.
        induction adjequiv.
        use subtypePath.
        * intro f.
          apply isaprop_disp_left_adjoint_equivalence.
          apply univalent_cat_is_univalent_2_1.
          apply bicatcatsunit_disp_prebicat_is_locally_univalent.
        * apply idpath.
  Defined.

  Lemma iso_from_ziso_from_iso {C : category} {x y : C} (f : C⟦x,y⟧) (pf : is_iso f) :
    (is_iso_from_is_z_iso f (is_z_iso_from_is_iso f pf) = pf).
  Proof.
  Admitted.


  (* This should already exists somewhere, but I can't find it *)
  Lemma iso_z_iso_equivalence {C : bicat_of_univ_cats} (IC ID : bicatcatsunit_disp_bicat C) :
     (iso IC ID) ≃ (z_iso IC ID).
  Proof.
    use make_weq.
    - apply iso_to_z_iso.
    - use isweq_iso.
      * apply z_iso_to_iso.
      * intro i.
        use total2_paths_b.
        -- apply idpath.
        -- apply transportb_transpose_right.
           etrans. { apply idpath_transportf. }
           cbn in *.
           Search (iso _ _ -> z_iso _ _).
           induction i as [i j].
           apply iso_from_ziso_from_iso.
      * intro i.
        unfold iso_to_z_iso.
        unfold z_iso_to_iso.
        cbn.
        use total2_paths_b.
        -- apply idpath.
        -- use total2_paths_b.
           ++ apply id_right.
           ++ use total2_paths_b.
              *** apply univalent_category_has_homsets.
              *** apply univalent_category_has_homsets.
  Defined.

  Lemma bicatcatsunit_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatsunit_disp_bicat.
  Proof.
    intros C D equalcats IC ID.
    induction equalcats.
    use weqhomot.
    - set (i1 := iso_dispadjequiv_equivalence C IC ID).
      set (i2 := iso_z_iso_equivalence IC ID).
      set (i3 := (_ ,, (pr2 C) IC ID)).
      exact (i1 ∘ i2 ∘ i3)%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence bicat_of_univ_cats  bicatcatsunit_disp_bicat).
        * exact univalent_cat_is_univalent_2_1.
        * exact bicatcatsunit_disp_prebicat_is_locally_univalent.
      + apply idpath.
  Defined.

  Lemma bicatcatsunit_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatsunit_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcatsunit_disp_prebicat_is_globally_univalent.
    - apply bicatcatsunit_disp_prebicat_is_locally_univalent.
  Defined.



End UnitLayer.
