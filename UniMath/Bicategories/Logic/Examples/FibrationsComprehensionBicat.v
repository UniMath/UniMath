(*******************************************************************

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

(**
 4. The comprehension bicategory of fibrations
 *)
Definition cleaving_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, total_univalent_category (pr1 D) ,, pr1_category _).
  - intros C₁ C₂ F D₁ D₂ FF.
    use make_disp_1cell_cod.
    + exact (total_functor (pr1 FF)).
    + use nat_z_iso_to_invertible_2cell.
      exact (total_functor_commute_z_iso (pr1 FF)).
  - intros C₁ C₂ F G α D₁ D₂ FF GG αα.
    use make_disp_2cell_cod.
    + exact (total_nat_trans (pr1 αα)).
    + abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  - intros C D.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_identity (pr11 D)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_nat_z_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_z_iso.
  - intros C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_comp (pr1 FF) (pr1 GG)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left, !id_right ;
           apply functor_id).
    + use is_disp_invertible_2cell_cod.
      use is_nat_z_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_z_iso.
Defined.

Definition cleaving_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      cleaving_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lassociator _ _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_rwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
Qed.

Definition cleaving_comprehension
  : disp_psfunctor
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact cleaving_comprehension_data.
  - exact cleaving_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_cleaving_comprehension
  : global_cartesian_disp_psfunctor cleaving_comprehension.
Proof.
  use preserves_global_lifts_to_cartesian.
  - exact univalent_cat_is_univalent_2.
  - exact (cod_disp_univalent_2 _ univalent_cat_is_univalent_2).
  - exact cleaving_of_cleaving_global_cleaving.
  - intros C₁ C₂ F D₁.
    use is_pb_to_cartesian_1cell.
    apply reindexing_has_pb_ump.
    apply is_isofibration_from_is_fibration.
    exact (pr2 D₁).
Defined.

Section LocalCartesianFibration.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F₁ F₂ : C₁ --> C₂}
          (α : F₁ ==> F₂)
          {D₁ : disp_bicat_of_cleaving C₁}
          {D₂ : disp_bicat_of_cleaving C₂}
          {FF₁ : D₁ -->[ F₁ ] D₂}
          {FF₂ : D₁ -->[ F₂ ] D₂}
          (αα : disp_2cells α FF₁ FF₂)
          (Hαα : ∏ (x : C₁ : univalent_category)
                   (xx : (pr1 D₁ : disp_univalent_category _) x),
                 is_cartesian ((pr11 αα) x xx))
          (G : bicat_of_univ_cats
                 ⟦ total_univalent_category (pr1 D₁)
                   ,
                   total_univalent_category (pr1 D₂) ⟧)
          (γ : G ==> total_functor (pr1 FF₂))
          (δp : (G ∙ pr1_category (pr11 D₂) : bicat_of_univ_cats ⟦ _ , _ ⟧)
                ==>
                total_functor (pr1 FF₁) ∙ pr1_category (pr11 D₂))
          (q : post_whisker γ (pr1_category (pr11 D₂))
               =
               nat_trans_comp
                 _ _ _
                 δp
                 (post_whisker (total_nat_trans (pr1 αα)) (pr1_category _))).

  Definition local_cartesian_cleaving_lift_data
    : nat_trans_data
        (pr1 G)
        (total_functor (pr1 FF₁)).
  Proof.
    refine (λ x, pr1 δp x ,, _) ; cbn.
    refine (cartesian_factorisation (Hαα (pr1 x) (pr2 x)) _ _).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (nat_trans_eq_pointwise q x)
             (pr2 (pr1 γ x))).
  Defined.

  Definition local_cartesian_cleaving_lift_is_nat_trans
    : is_nat_trans _ _ local_cartesian_cleaving_lift_data.
  Proof.
    intros x y f ; cbn.
    use total2_paths_f.
    - exact (nat_trans_ax δp x y f).
    - use (cartesian_factorisation_unique (Hαα (pr1 y) (pr2 y))).
      cbn.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply disp_nat_trans_ax.
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (fiber_paths (nat_trans_ax γ _ _ f)).
      }
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition local_cartesian_cleaving_lift
    : G ==> total_functor (pr1 FF₁).
  Proof.
    use make_nat_trans.
    - exact local_cartesian_cleaving_lift_data.
    - exact local_cartesian_cleaving_lift_is_nat_trans.
  Defined.

  Definition local_cartesian_cleaving_lift_over
    : local_cartesian_cleaving_lift ▹ _ = δp.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    apply idpath.
  Qed.

  Definition local_cartesian_cleaving_lift_comm
    : local_cartesian_cleaving_lift • total_nat_trans (pr1 αα)
      =
      γ.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    cbn.
    use total2_paths_f.
    - exact (!(nat_trans_eq_pointwise q x)).
    - cbn.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition local_cartesian_cleaving_lift_unique
    : isaprop
        (∑ δ,
         δ ▹ _ = δp
         ×
         δ • total_nat_trans (pr1 αα) = γ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use total2_paths_f.
    - exact (nat_trans_eq_pointwise (pr12 φ₁) x
             @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
    - use (cartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      rewrite mor_disp_transportf_postwhisker.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₁) x))).
      }
      refine (!_).
      etrans.
      {
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₂) x))).
      }
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.
End LocalCartesianFibration.

Definition local_cartesian_cleaving_comprehension
  : local_cartesian_disp_psfunctor cleaving_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α D₁ D₂ FF₁ FF₂ αα Hαα.
  apply is_cartesian_2cell_sfib_to_is_cartesian_2cell ; cbn.
  pose (cleaving_of_cleaving_cartesian_2cell_is_pointwise_cartesian _ Hαα) as p.
  intros G γ δp q.
  use iscontraprop1.
  - exact (local_cartesian_cleaving_lift_unique α αα p G γ δp).
  - simple refine (_ ,, _ ,, _).
    + exact (local_cartesian_cleaving_lift α αα p G γ δp q).
    + exact (local_cartesian_cleaving_lift_over α αα p G γ δp q).
    + exact (local_cartesian_cleaving_lift_comm α αα p G γ δp q).
Defined.

Definition cleaving_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat_structure.
  - exact disp_bicat_of_cleaving.
  - exact cleaving_comprehension.
  - exact cleaving_of_cleaving_global_cleaving.
  - exact global_cartesian_cleaving_comprehension.
Defined.

Definition cleaving_comprehension_is_contravariant
  : is_contravariant cleaving_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact cleaving_of_cleaving_local_cleaving.
  - exact cleaving_of_cleaving_lwhisker_cartesian.
  - exact cleaving_of_cleaving_rwhisker_cartesian.
  - exact local_cartesian_cleaving_comprehension.
Defined.

Definition cleaving_contravariant_comprehension_bicat
  : contravariant_comprehension_bicat
  := _ ,, _ ,, cleaving_comprehension_is_contravariant.
