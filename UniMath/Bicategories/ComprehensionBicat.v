(*******************************************************************

 Comprehension bicategories

 In this file we define comprehension bicategories and we
 construct examples of them.

 1. Comprehension bicategories
 2. The trivial comprehension bicategory
 3. Locally groupoidal bicategories with pullbacks
 4. The comprehension bicategory of fibrations
 5. The comprehension bicategory of opfibrations

 *******************************************************************)
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
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.TrivialCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.OpFibrationCleaving.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

(**
 1. Comprehension bicategories
 *)
Definition comprehension_bicat
           (B : bicat)
  : UU
  := ∑ (D : disp_bicat B)
       (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B)),
     global_cleaving D × global_cartesian_disp_psfunctor χ.

Definition make_comprehension_bicat
           (B : bicat)
           (D : disp_bicat B)
           (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B))
           (HD : global_cleaving D)
           (Hχ : global_cartesian_disp_psfunctor χ)
  : comprehension_bicat B
  := D ,, χ ,, HD ,, Hχ.

(** Projections of a comprehension bicategory *)
Definition ty_of
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : disp_bicat B
  := pr1 comp_B.

Definition comp_of
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : disp_psfunctor (ty_of comp_B) (cod_disp_bicat B) (id_psfunctor B)
  := pr12 comp_B.

Definition ty_of_global_cleaving
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : global_cleaving (ty_of comp_B)
  := pr122 comp_B.

Definition comp_of_global_cartesian
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : global_cartesian_disp_psfunctor (comp_of comp_B)
  := pr222 comp_B.

(** Variances of comprehension bicategories *)
Definition is_covariant
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_opcleaving D
     × lwhisker_opcartesian D
     × rwhisker_opcartesian D
     × local_opcartesian_disp_psfunctor χ.

Definition is_contravariant
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_cleaving D
     × lwhisker_cartesian D
     × rwhisker_cartesian D
     × local_cartesian_disp_psfunctor χ.

(**
 2. The trivial comprehension bicategory
 *)
Section TrivialCompBicat.
  Context (B : bicat_with_binprod).

  Definition trivial_comprehension_data
    : disp_psfunctor_data
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - intros x y.
      use make_ar.
      + exact (x ⊗ y).
      + exact π₁.
    - intros x₁ x₂ f y₁ y₂ g.
      use make_disp_1cell_cod.
      + exact (f ⊗₁ g).
      + apply inv_of_invertible_2cell.
        apply pair_1cell_pr1.
    - intros x₁ x₂ f₁ f₂ α y₁ y₂ g₁ g₂ β.
      use make_disp_2cell_cod.
      + exact (α ⊗₂ β).
      + abstract
          (unfold coherent_homot ;
           cbn ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso | ] ;
           cbn ;
           apply prod_2cell_pr1_alt).
    - intro ; intros ; simpl.
      simple refine (_ ,, _).
      + use make_disp_2cell_cod.
        * exact ((pair_1cell_id_id_invertible _ _ _)^-1).
        * abstract
            (unfold coherent_homot ;
             cbn ;
             refine (maponpaths _ (binprod_ump_2cell_pr1 _ _ _) @ _) ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite lwhisker_id2 ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite linvunitor_lunitor ;
             rewrite id2_left ;
             apply runitor_rinvunitor).
      + use is_disp_invertible_2cell_cod.
        cbn.
        apply binprod_ump_2cell_invertible ; is_iso.
    - intro ; intros ; simpl.
      simple refine (_ ,, _).
      + use make_disp_2cell_cod.
        * apply pair_1cell_comp.
        * abstract
            (unfold coherent_homot ;
             cbn ;
             rewrite !vassocl ;
             etrans ; [ do 5 apply maponpaths ; apply binprod_ump_2cell_pr1 | ] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             etrans ;
             [ do 4 apply maponpaths ;
               rewrite !vassocr ;
               rewrite lassociator_rassociator ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ do 3 apply maponpaths ;
               rewrite !vassocr ;
               rewrite lwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite lwhisker_id2 ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ do 2 apply maponpaths ;
               rewrite !vassocr ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ apply maponpaths ;
               rewrite !vassocr ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             rewrite lassociator_rassociator ;
             rewrite lwhisker_id2 ;
             apply idpath).
      + use is_disp_invertible_2cell_cod.
        cbn.
        apply pair_1cell_comp_invertible.
  Defined.

  Definition trivial_comprehension_is_disp_psfunctor
    : is_disp_psfunctor
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B)
        trivial_comprehension_data.
  Proof.
  (*
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).

    cbn ;
    unfold transportb.
    rewrite pr1_transportf, transportf_const ;
    cbn.
  - rewrite pair_2cell_id_id.
    apply idpath.
  - rewrite pair_2cell_comp.
    apply idpath.
  - use binprod_ump_2cell_unique_alt.
    + apply (pr2 B).
    + rewrite <- !rwhisker_vcomp.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocl.
      apply TODO.
    + apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
Qed.
   *)
  Admitted.

  Definition trivial_comprehension
    : disp_psfunctor
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _).
    - exact trivial_comprehension_data.
    - exact trivial_comprehension_is_disp_psfunctor.
  Defined.

  Definition global_cartesian_trivial_comprehension
    : global_cartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f c₁ c₂ g Hg ; cbn in *.
    apply is_pb_to_cartesian_1cell.
    simpl.
    pose (g_equiv := trivial_cartesian_1cell_is_adj_equiv _ _ _ _ Hg).
  Admitted.

  Definition local_cartesian_trivial_comprehension
    : local_cartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f₁ f₂ α c₁ c₂ g₁ g₂ β Hβ ; cbn in *.
  Admitted.

  Definition local_opcartesian_trivial_comprehension
    : local_opcartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f₁ f₂ α c₁ c₂ g₁ g₂ β Hβ ; cbn in *.
  Admitted.

  Definition trivial_comprehension_bicat
    : comprehension_bicat B.
  Proof.
    use make_comprehension_bicat.
    - exact (trivial_displayed_bicat B B).
    - exact trivial_comprehension.
    - exact (trivial_cleaving_of_bicats B B).
    - exact global_cartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_covariant
    : is_covariant trivial_comprehension_bicat.
  Proof.
    repeat split.
    - exact (trivial_local_opcleaving B B).
    - exact (trivial_lwhisker_opcartesian B B).
    - exact (trivial_rwhisker_opcartesian B B).
    - exact local_opcartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_contravariant
    : is_contravariant trivial_comprehension_bicat.
  Proof.
    repeat split.
    - exact (trivial_local_cleaving B B).
    - exact (trivial_lwhisker_cartesian B B).
    - exact (trivial_rwhisker_cartesian B B).
    - exact local_cartesian_trivial_comprehension.
  Defined.
End TrivialCompBicat.

(**
 3. Locally groupoidal bicategories with pullbacks
 *)
Section PullbackComprehension.
  Context (B : bicat)
          (B_pb : has_pb B).

  Definition pb_comprehension
    : comprehension_bicat B.
  Proof.
    use make_comprehension_bicat.
    - exact (cod_disp_bicat B).
    - exact (disp_pseudo_id (cod_disp_bicat B)).
    - exact (cod_global_cleaving B B_pb).
    - exact (global_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Context (HB : locally_groupoid B).

  Definition locally_grpd_pb_comprehension_is_covariant
    : is_covariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_opcleaving _ HB).
    - exact (cod_cleaving_lwhisker_opcartesian _ HB).
    - exact (cod_cleaving_rwhisker_opcartesian _ HB).
    - exact (local_opcartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Definition locally_grpd_pb_comprehension_is_contravariant
    : is_contravariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_cleaving _ HB).
    - exact (cod_cleaving_lwhisker_cartesian _ HB).
    - exact (cod_cleaving_rwhisker_cartesian _ HB).
    - exact (local_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.
End PullbackComprehension.

(**
 4. The comprehension bicategory of fibrations
 *)
Definition fibration_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_fibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  (*
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, total_univalent_category (pr1 D) ,, pr1_category _).
  - intros C₁ C₂ F D₁ D₂ HF.
    use make_disp_1cell_cod.
    + exact (total_functor (pr1 HF)).
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
    use make_disp_2cell_cod.
    + use make_nat_trans.
      * exact (λ x, pr1 α (pr1 x) ,, pr11 αα _ (pr2 x)).
      * intros x y f ; cbn.
        admit.
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
   *)
Admitted.

Definition fibration_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_fibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      fibration_comprehension_data.
Proof.
  (*
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]) ;
    refine (_ @ !(transportb_cell_of_internal_sfib_over _ _ _)) ;
    (apply nat_trans_eq ; [ intro ; apply total_category | ]) ;
    intro ; simpl ; try (apply idpath).
   *)
Admitted.


Definition fibration_comprehension
  : disp_psfunctor
      disp_bicat_of_fibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact fibration_comprehension_data.
  - exact fibration_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_fibration_comprehension
  : global_cartesian_disp_psfunctor fibration_comprehension.
Proof.
Admitted.

Definition local_cartesian_fibration_comprehension
  : local_cartesian_disp_psfunctor fibration_comprehension.
Proof.
Admitted.

Definition fibration_comprehension_bicat
  : comprehension_bicat bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat.
  - exact disp_bicat_of_fibs.
  - exact fibration_comprehension.
  - exact cleaving_of_fibs.
  - exact global_cartesian_fibration_comprehension.
Defined.

Definition fibration_comprehension_is_contravariant
  : is_contravariant fibration_comprehension_bicat.
Proof.
  repeat split.
  - exact cleaving_of_fibs_local_cleaving.
  - exact cleaving_of_fibs_lwhisker_cartesian.
  - exact cleaving_of_fibs_rwhisker_cartesian.
  - exact local_cartesian_fibration_comprehension.
Defined.

(**
 4. The comprehension bicategory of opfibrations
 *)
Definition opfibration_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_opfibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  (*
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, total_univalent_category (pr1 D) ,, pr1_category _).
  - intros C₁ C₂ F D₁ D₂ HF.
    use make_disp_1cell_cod.
    + exact (total_functor (pr1 HF)).
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
    use make_disp_2cell_cod.
    + use make_nat_trans.
      * exact (λ x, pr1 α (pr1 x) ,, pr11 αα _ (pr2 x)).
      * intros x y f ; cbn.
        admit.
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
   *)
Admitted.

Definition opfibration_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_opfibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      opfibration_comprehension_data.
Proof.
  (*
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]) ;
    refine (_ @ !(transportb_cell_of_internal_sfib_over _ _ _)) ;
    (apply nat_trans_eq ; [ intro ; apply total_category | ]) ;
    intro ; simpl ; try (apply idpath).
   *)
Admitted.


Definition opfibration_comprehension
  : disp_psfunctor
      disp_bicat_of_opfibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact opfibration_comprehension_data.
  - exact opfibration_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_opfibration_comprehension
  : global_cartesian_disp_psfunctor opfibration_comprehension.
Proof.
Admitted.

Definition local_opcartesian_opfibration_comprehension
  : local_opcartesian_disp_psfunctor opfibration_comprehension.
Proof.
Admitted.

Definition opfibration_comprehension_bicat
  : comprehension_bicat bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat.
  - exact disp_bicat_of_opfibs.
  - exact opfibration_comprehension.
  - exact opfibs_global_cleaving.
  - exact global_cartesian_opfibration_comprehension.
Defined.

Definition opfibration_comprehension_is_contravariant
  : is_covariant opfibration_comprehension_bicat.
Proof.
  repeat split.
  - exact cleaving_of_opfibs_local_opcleaving.
  - exact cleaving_of_opfibs_lwhisker_opcartesian.
  - exact cleaving_of_opfibs_rwhisker_opcartesian.
  - exact local_opcartesian_opfibration_comprehension.
Defined.
