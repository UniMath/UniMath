Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Faithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CodomainFibs.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

Definition comprehension_bicat
  : UU
  := ∑ (B : bicat)
       (D : disp_bicat B)
       (χ : disp_psfunctor D (cod_sfibs B) (id_psfunctor B)),
     cleaving_of_bicats D × cartesian_disp_psfunctor χ.

Definition make_comprehension_bicat
           (B : bicat)
           (D : disp_bicat B)
           (χ : disp_psfunctor D (cod_sfibs B) (id_psfunctor B))
           (HD : cleaving_of_bicats D)
           (Hχ : cartesian_disp_psfunctor χ)
  : comprehension_bicat
  := B ,, D ,, χ ,, HD ,, Hχ.

Definition cod_to_sfibs_data
           (B : bicat)
           (HB : locally_groupoid B)
  : disp_psfunctor_data
      (cod_disp_bicat B)
      (cod_sfibs B)
      (id_psfunctor B).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - intros x hx.
    refine (pr1 hx ,, pr2 hx ,, _).
    apply (locally_grpd_internal_sfib HB).
  - simpl.
    intros x uy f hx hy hf.
    simple refine (pr1 hf ,, (_ ,, _)) ; cbn.
    + apply (locally_grpd_preserves_cartesian HB).
    + exact (pr2 hf).
  - exact (λ _ _ _ _ _ _ _ _ _ hα, hα).
  - intro ; intros ; simpl.
    use make_cod_sfibs_disp_invertible_2cell.
    + use make_cell_of_internal_sfib_over.
      * apply id2.
      * abstract
          (unfold cell_of_internal_sfib_over_homot ;
           cbn ;
           rewrite id2_rwhisker, id2_right ;
           rewrite lwhisker_id2, id2_left ;
           apply idpath).
    + cbn.
      is_iso.
  - intro ; intros ; simpl.
    use make_cod_sfibs_disp_invertible_2cell.
    + use make_cell_of_internal_sfib_over.
      * apply id2.
      * abstract
          (unfold cell_of_internal_sfib_over_homot ;
           cbn ;
           rewrite id2_rwhisker, id2_right ;
           rewrite lwhisker_id2, id2_left ;
           apply idpath).
    + cbn.
      is_iso.
Defined.

Definition cod_to_sfibs_is_disp_psfunctor
           (B : bicat)
           (HB : locally_groupoid B)
  : is_disp_psfunctor
      (cod_disp_bicat B)
      (cod_sfibs B)
      (id_psfunctor B)
      (cod_to_sfibs_data B HB).
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]) ; simpl ;
      rewrite transportb_cell_of_internal_sfib_over ; cbn.
  - apply idpath.
  - apply idpath.
  - rewrite id2_rwhisker, !id2_left.
    apply idpath.
  - rewrite lwhisker_id2, !id2_left.
    apply idpath.
  - rewrite id2_rwhisker, lwhisker_id2, !id2_left, !id2_right.
    apply idpath.
  - rewrite id2_left, id2_right.
    apply idpath.
  - rewrite id2_left, id2_right.
    apply idpath.
Qed.

Definition cod_to_sfibs
           (B : bicat)
           (HB : locally_groupoid B)
  : disp_psfunctor
      (cod_disp_bicat B)
      (cod_sfibs B)
      (id_psfunctor B).
Proof.
  simple refine (_ ,, _).
  - exact (cod_to_sfibs_data B HB).
  - exact (cod_to_sfibs_is_disp_psfunctor B HB).
Defined.

Definition locally_grpd_pb_comprehension
           (B : bicat)
           (HB : locally_groupoid B)
           (B_pb : has_pb B)
  : comprehension_bicat.
Proof.
  use make_comprehension_bicat.
  - exact B.
  - exact (cod_disp_bicat B).
  - exact (cod_to_sfibs B HB).
  - exact (cod_cleaving_of_bicats B HB B_pb).
  - apply TODO.
Defined.

Definition disp_map_bicat_to_comprehension_bicat
           (B : bicat)
           (P : disp_map_bicat B)
  : comprehension_bicat.
Proof.
  use make_comprehension_bicat.
  - exact B.
  - exact (disp_map_bicat_to_disp_bicat P).
  - exact (disp_map_bicat_inclusion P).
  - apply TODO.
  - apply TODO.
Defined.

Definition fibration_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_fibs
      (cod_sfibs bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - refine (λ C D, total_univalent_category (pr1 D) ,, pr1_category _ ,, _).
    apply TODO.
  - intros C₁ C₂ F D₁ D₂ HF ; simpl.
    use make_mor_of_internal_sfib_over.
    + exact (total_functor (pr1 HF)).
    + apply TODO.
    + use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      * use make_nat_trans.
        ** exact (λ _, identity _).
        ** abstract
             (intros ? ? ? ;
              cbn ;
              rewrite id_left, id_right ;
              apply idpath).
      * intro.
        apply identity_is_iso.
  - intros C₁ C₂ F G α D₁ D₂ FF GG αα.
    use make_cell_of_internal_sfib_over.
    + use make_nat_trans.
      * intros x.
        exact (pr1 α (pr1 x) ,, pr11 αα _ (pr2 x)).
      * apply TODO.
    + apply TODO.
  - intros C D.
    use make_cod_sfibs_disp_invertible_2cell.
    + use make_cell_of_internal_sfib_over.
      * use make_nat_trans.
        ** exact (λ _, identity _).
        ** abstract
             (intros ? ? ? ; simpl ;
              refine (@id_right (total_category _) _ _ _ @ _) ;
              exact (!(@id_left (total_category _) _ _ _))).
      * abstract
          (simpl ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
  - intros C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG.
    use make_cod_sfibs_disp_invertible_2cell.
    + use make_cell_of_internal_sfib_over.
      * use make_nat_trans.
        ** exact (λ _, identity _).
        ** intros ? ? ? ; simpl.
           apply TODO.
      * abstract
          (simpl ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left, !id_right ;
           apply functor_id).
    + use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
Defined.

Definition fibration_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_fibs
      (cod_sfibs bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      fibration_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]) ;
    refine (_ @ !(transportb_cell_of_internal_sfib_over _ _ _)) ;
    (apply nat_trans_eq ; [ intro ; apply total_category | ]) ;
    intro ; simpl ; try (apply idpath).
Admitted.


Definition fibration_comprehension
  : disp_psfunctor
      disp_bicat_of_fibs
      (cod_sfibs bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact fibration_comprehension_data.
  - exact fibration_comprehension_is_disp_psfunctor.
Defined.

Definition fibration_comprehension_bicat
  : comprehension_bicat.
Proof.
  use make_comprehension_bicat.
  - exact bicat_of_univ_cats.
  - exact disp_bicat_of_fibs.
  - exact fibration_comprehension.
  - exact (cleaving_of_fibs TODO TODO).
  - admit.
Admitted.
