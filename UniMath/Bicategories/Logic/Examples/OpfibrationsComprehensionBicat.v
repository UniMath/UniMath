(*******************************************************************

 The comprehension bicategory of opfibrations

 Contents
 1. The comprehension pseudofunctor
 2. Preservation of cartesian 1-cells
 3. Preservation of opcartesian 2-cells
 4. The comprehension bicategory

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
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.OpFibrationCleaving.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

(**
 1. The comprehension pseudofunctor
 *)
Definition opcleaving_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_opcleaving
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

Definition opcleaving_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_opcleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      opcleaving_comprehension_data.
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

Definition opcleaving_comprehension
  : disp_psfunctor
      disp_bicat_of_opcleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact opcleaving_comprehension_data.
  - exact opcleaving_comprehension_is_disp_psfunctor.
Defined.

(**
 2. Preservation of cartesian 1-cells
 *)
Definition global_cartesian_opcleaving_comprehension
  : global_cartesian_disp_psfunctor opcleaving_comprehension.
Proof.
  use preserves_global_lifts_to_cartesian.
  - exact univalent_cat_is_univalent_2.
  - exact (cod_disp_univalent_2 _ univalent_cat_is_univalent_2).
  - exact opcleaving_global_cleaving.
  - intros C₁ C₂ F D₁.
    use is_pb_to_cartesian_1cell.
    apply reindexing_has_pb_ump.
    apply iso_cleaving_from_opcleaving.
    exact (pr2 D₁).
Defined.

(**
 3. Preservation of opcartesian 2-cells
 *)
Section LocalOpCartesianOpFibration.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F₁ F₂ : C₁ --> C₂}
          (α : F₁ ==> F₂)
          {D₁ : disp_bicat_of_opcleaving C₁}
          {D₂ : disp_bicat_of_opcleaving C₂}
          {FF₁ : D₁ -->[ F₁ ] D₂}
          {FF₂ : D₁ -->[ F₂ ] D₂}
          (αα : disp_2cells α FF₁ FF₂)
          (Hαα : ∏ (x : C₁ : univalent_category)
                   (xx : (pr1 D₁ : disp_univalent_category _) x),
                 is_opcartesian ((pr11 αα) x xx))
          (G : bicat_of_univ_cats
                 ⟦ total_univalent_category (pr1 D₁)
                   ,
                   total_univalent_category (pr1 D₂) ⟧)
          (tot_FF₁ := (total_functor (pr1 FF₁)
                       : bicat_of_univ_cats
                           ⟦ total_univalent_category (pr1 D₁)
                             ,
                             total_univalent_category (pr1 D₂) ⟧))
          (tot_FF₂ := (total_functor (pr1 FF₂)
                       : bicat_of_univ_cats
                           ⟦ total_univalent_category (pr1 D₁)
                             ,
                             total_univalent_category (pr1 D₂) ⟧))
          (tot_αα := total_nat_trans (pr1 αα) : tot_FF₁ ==> tot_FF₂)
          (γ : tot_FF₁ ==> G)
          (δp : tot_FF₂ · pr1_category _ ==> G · pr1_category _)
          (q : post_whisker γ (pr1_category (pr11 D₂))
               =
               nat_trans_comp
                 _ _ _
                 (post_whisker (total_nat_trans (pr1 αα)) (pr1_category _))
                 δp).

  Definition local_opcartesian_opcleaving_lift_data
    : nat_trans_data (pr1 tot_FF₂) (pr1 G).
  Proof.
    refine (λ x, pr1 δp x ,, _) ; cbn.
    refine (opcartesian_factorisation (Hαα (pr1 x) (pr2 x)) _ _).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (nat_trans_eq_pointwise q x)
             (pr2 (pr1 γ x))).
  Defined.

  Definition local_opcartesian_opcleaving_lift_is_nat_trans
    : is_nat_trans _ _ local_opcartesian_opcleaving_lift_data.
  Proof.
    intros x y f ; cbn.
    use total2_paths_f.
    - exact (nat_trans_ax δp x y f).
    - use (opcartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      cbn.
      rewrite assoc_disp.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        exact (transportf_transpose_left (disp_nat_trans_ax (pr1 αα) (pr2 f))).
      }
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right (fiber_paths (nat_trans_ax γ _ _ f))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition local_opcartesian_opcleaving_lift
    : tot_FF₂ ==> G.
  Proof.
    use make_nat_trans.
    - exact local_opcartesian_opcleaving_lift_data.
    - exact local_opcartesian_opcleaving_lift_is_nat_trans.
  Defined.

  Definition local_opcartesian_opcleaving_lift_over
    : local_opcartesian_opcleaving_lift ▹ _ = δp.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    apply idpath.
  Qed.

  Definition local_opcartesian_opcleaving_lift_comm
    : tot_αα • local_opcartesian_opcleaving_lift
      =
      γ.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    cbn.
    use total2_paths_f.
    - exact (!(nat_trans_eq_pointwise q x)).
    - cbn.
      rewrite opcartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition local_opcartesian_opcleaving_lift_unique
    : isaprop
        (∑ δ,
         δ ▹ _ = δp
         ×
         tot_αα • δ = γ).
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
    - use (opcartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      rewrite mor_disp_transportf_prewhisker.
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
End LocalOpCartesianOpFibration.

Definition local_opcartesian_opcleaving_comprehension
  : local_opcartesian_disp_psfunctor opcleaving_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α D₁ D₂ FF₁ FF₂ αα Hαα.
  apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell ; cbn.
  pose (opcleaving_of_opcleaving_opcartesian_2cell_is_pointwise_opcartesian _ Hαα) as p.
  intros G γ δp q.
  use iscontraprop1.
  - exact (local_opcartesian_opcleaving_lift_unique α αα p G γ δp).
  - simple refine (_ ,, _ ,, _).
    + exact (local_opcartesian_opcleaving_lift α αα p G γ δp q).
    + exact (local_opcartesian_opcleaving_lift_over α αα p G γ δp q).
    + exact (local_opcartesian_opcleaving_lift_comm α αα p G γ δp q).
Defined.

(**
 4. The comprehension bicategory
 *)
Definition opcleaving_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat_structure.
  - exact disp_bicat_of_opcleaving.
  - exact opcleaving_comprehension.
  - exact opcleaving_global_cleaving.
  - exact global_cartesian_opcleaving_comprehension.
Defined.

Definition opcleaving_comprehension_is_covariant
  : is_covariant opcleaving_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact cleaving_of_opcleaving_local_opcleaving.
  - exact cleaving_of_opcleaving_lwhisker_opcartesian.
  - exact cleaving_of_opcleaving_rwhisker_opcartesian.
  - exact local_opcartesian_opcleaving_comprehension.
Defined.

Definition opcleaving_comprehension_bicat
  : comprehension_bicat
  := _ ,, _ ,, opcleaving_comprehension_is_covariant.
