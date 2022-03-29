(* In this file we construct the category of monoidal categories as the total category
   of a displayed category of the category of categories.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalNaturalTransformationsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section BiategoryOfMonoidalCategories.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Definition catcats_disp_ob_mor : disp_cat_ob_mor bicat_of_cats.
  Proof.
    use tpair.
    - exact (λ C, monoidal C).
    - exact (λ C D MC MD F, fmonoidal MC MD F).
  Defined.


  Definition catcats_disp_id_comp : disp_cat_id_comp bicat_of_cats catcats_disp_ob_mor.
  Proof.
    use tpair.
    - intros C MC.
      apply fmonoidal_identity.
    - intros C D E F G MC MD ME.
      exact (λ MF MG, fmonoidal_composition MF MG).
  Defined.

  Definition catcats_disp_catdata : disp_cat_data bicat_of_cats
    := (catcats_disp_ob_mor,,catcats_disp_id_comp).

  Definition bicatcats_disp_2cell_struct : disp_2cell_struct catcats_disp_ob_mor.
  Proof.
    intros C D F G α MC MD.
    exact (λ MF MG, nmonoidal MF MG α).
  Defined.

  Definition bicatcats_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_cats
    := (catcats_disp_catdata,, bicatcats_disp_2cell_struct).

  Definition bicatcats_disp_prebicat_ops : disp_prebicat_ops bicatcats_disp_prebicat_1_id_comp_cells.
  Proof.
    use tpair.
    - intros C D F MC MD.
      exact (λ MF, nmonoidal_identity MF).
    - use tpair.
      + intros C D F MC MD MF.
        unfold disp_2cells.
        simpl.
        unfold bicatcats_disp_2cell_struct.
        use tpair.
        * unfold preservesunit_commutes.
          cbn.
          rewrite id_right.
          rewrite functor_id.
          apply id_right.
        * intros x y.
          cbn.
          rewrite id_right.
          rewrite bifunctor_distributes_over_id.
          -- rewrite id_left.
             rewrite functor_id.
             apply id_right.
          -- apply bifunctor_leftid.
          -- apply bifunctor_rightid.
      + use tpair.
        * intros C D F MC MD MF.
          unfold disp_2cells.
          simpl.
          unfold bicatcats_disp_2cell_struct.
          use tpair.
          -- unfold preservesunit_commutes.
             unfold fmonoidal_preservesunit.
             simpl.
             rewrite id_right.
             apply id_left.
          -- intros x y.
             cbn.
             rewrite id_right.
             rewrite bifunctor_distributes_over_id.
             ++ rewrite id_left.
                apply idpath.
             ++ apply bifunctor_leftid.
             ++ apply bifunctor_rightid.
        * use tpair.
          -- intros C D F MC MD MF.
             simpl.
             unfold bicatcats_disp_2cell_struct.
             use tpair.
             ++ unfold preservesunit_commutes.
                unfold fmonoidal_preservesunit.
                simpl.
                rewrite functor_id.
                rewrite id_right.
                rewrite id_right.
                apply idpath.
             ++ intros x y.
                unfold fmonoidal_preservestensordata.
                cbn.
                rewrite bifunctor_distributes_over_id.
                ** rewrite id_left.
                   rewrite functor_id.
                   rewrite id_right.
                   rewrite id_right.
                   apply idpath.
                ** apply bifunctor_leftid.
                ** apply bifunctor_rightid.
          -- use tpair.
             ++ intros C D F MC MD MF.
                use tpair.
                ** unfold preservesunit_commutes.
                   unfold fmonoidal_preservesunit.
                   simpl.
                   rewrite id_left.
                   apply id_right.
                ** intros x y.
                   unfold fmonoidal_preservestensordata.
                   simpl.
                   rewrite bifunctor_distributes_over_id.
                   --- rewrite id_left.
                       rewrite id_left.
                       apply id_right.
                   --- apply bifunctor_leftid.
                   --- apply bifunctor_rightid.
             ++ use tpair.
                ** intros C C' D D' F G H MC MC' MD MD' MF MG MH.
                   simpl.
                   unfold bicatcats_disp_2cell_struct.
                   use tpair.
                   --- unfold preservesunit_commutes.
                       unfold fmonoidal_preservesunit.
                       simpl.
                       unfold fmonoidal_preservesunit.
                       rewrite functor_comp.
                       rewrite id_right.
                       apply assoc.
                   --- intros x y.
                       unfold fmonoidal_preservestensordata.
                       simpl.
                       rewrite functor_comp.
                       rewrite bifunctor_distributes_over_id.
                       +++ rewrite id_right.
                           rewrite id_left.
                           apply assoc.
                       +++ apply bifunctor_leftid.
                       +++ apply bifunctor_rightid.
                ** use tpair.
                   --- intros C C' D D' F G H MC MC' MD MD' MF MG MH.
                       unfold bicatcats_disp_2cell_struct.
                       use tpair.
                       +++ unfold preservesunit_commutes.
                           unfold fmonoidal_preservesunit.
                           simpl.
                           unfold fmonoidal_preservesunit.
                           rewrite functor_comp.
                           rewrite id_right.
                           apply assoc'.
                       +++ intros x y.
                           unfold fmonoidal_preservestensordata.
                           simpl.
                           rewrite functor_comp.
                           rewrite bifunctor_distributes_over_id.
                           *** rewrite id_right.
                               rewrite id_left.
                               apply assoc'.
                           *** apply bifunctor_leftid.
                           *** apply bifunctor_rightid.
                   --- use tpair.
                       +++ intros C D F G H α β MC MD MF MG MH Mα Mβ.
                           unfold disp_2cells.
                           simpl.
                           use tpair.
                           *** unfold preservesunit_commutes.
                               unfold vcomp2.
                               simpl.
                               rewrite assoc.
                               rewrite (pr1 Mα).
                               apply (pr1 Mβ).
                           *** intros x y.
                               unfold vcomp2.
                               simpl.
                               rewrite assoc.
                               rewrite (pr2 Mα).
                               rewrite assoc'.
                               rewrite (pr2 Mβ).
                               rewrite assoc.
                               rewrite bifunctor_distributes_over_comp.
                               ---- apply idpath.
                               ---- apply bifunctor_leftcomp.
                               ---- apply bifunctor_rightcomp.
                               ---- apply bifunctor_equalwhiskers.
                       +++ use tpair.
                           *** intros C D D' F G G' α MC MD MD' MF MG MG' Mα.
                               use tpair.
                               ---- unfold preservesunit_commutes.
                                    simpl.
                                    rewrite assoc'.
                                    rewrite (pr2 α).
                                    rewrite assoc.
                                    etrans. {
                                      apply cancel_postcomposition.
                                      Check pr1 Mα.
                                      (*  This is where my problem lies,
                                          pr1 Mα is a proof of
                                          fmonoidal_preservesunit MG · α I_{MD} = fmonoidal MG
                                          The left hand side is  precisely the current goal,
                                          but it seems that Coq doesn't know that
                                          α I_{MD} = (pr1 α) I_{MD}
                                      *)
                                      rewrite (pr1 Mα).
                                      admit.


































  Definition bicatcats_disp_prebicat_data : disp_prebicat_data
    :=

  Definition bicatcats_disp_id2_left_law : disp_id2_left_law




  Definition catcats_disp_cat_axioms : disp_cat_axioms catcats catcats_disp_catdata.
  Proof.
    use tpair.
    - intros C D F MC MD MF.
      admit.
    - use tpair.
      + intros C D F MC MD MF.
        admit.
      + use tpair.
        * C C' D D' F G H MC MC' MD MD' MF MG MH.
          admit.
        * intros C D F MC MD.
          (* is a set, so something like use homset_property *)
  Defined.

  Definition catcats_disp_cat : disp_cat catcats
    := (catcats_disp_catdata,,catcats_disp_cat_axioms).
