(***********************************************************************

 Reindexing displayed bicategories over the bicategory of categories

 We prove that every displayed bicategory on the bicategory of
 (not necessarily univalent) categories gives rise to a displayed
 bicategory on the bicategory of univalent categories. This construction
 keeps the displayed objects/1-cells/2-cells to be the same, and thus
 the composition/identities are inherited as well.

 For displayed categories, we have a reindexing operator: if we have a
 displayed category `D` over `C₂` and a functor `F : C₁ ⟶ C₂`, then we
 get a displayed category `F^* D` over `C₁` and a displayed functor
 `FF : F^* D ⟶ D` over `F`. The construction we discuss in this file, is
 a special case of the bicategorical analogue of this operation where we
 use the inclusion.

 Hence, we look at two constructions:
 1. The reindexed displayed bicategory [disp_bicat_on_cat_to_univ_cat]
 2. The displayed pseudofunctor [disp_psfunctor_on_cat_to_univ_cat]

 Contents
 1. The reindexed displayed bicategory
 2. Properties of the reindexed displayed bicategory
 3. The displayed pseudofunctor over the inclusion

 ***********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Local Open Scope cat.

Section DispBicatOnCats.
  Context (D : disp_bicat bicat_of_cats).

  (**
   1. The reindexed displayed bicategory
   *)
  Definition disp_cat_ob_mor_on_cat_to_univ_cat
    : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact (λ C, D (pr1 C)).
    - exact (λ C₁ C₂ CC₁ CC₂ F, CC₁ -->[ F ] CC₂).
  Defined.

  Definition disp_cat_id_comp_on_cat_to_univ_cat
    : disp_cat_id_comp
        bicat_of_univ_cats
        disp_cat_ob_mor_on_cat_to_univ_cat.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ C CC, id_disp _).
    - exact (λ C₁ C₂ C₃ F G CC₁ CC₂ CC₃ FF GG, FF ;; GG)%mor_disp.
  Defined.

  Definition disp_cat_data_on_cat_to_univ_cat
    : disp_cat_data bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_ob_mor_on_cat_to_univ_cat.
    - exact disp_cat_id_comp_on_cat_to_univ_cat.
  Defined.

  Definition disp_prebicat_1_id_comp_cells_on_cat_to_univ_cat
    : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_data_on_cat_to_univ_cat.
    - exact (λ (C₁ C₂ : univalent_category)
               (F G : bicat_of_cats ⟦ pr1 C₁ , pr1 C₂ ⟧)
               (τ : F ==> G)
               (CC₁ : D (pr1 C₁))
               (CC₂ : D (pr1 C₂))
               (FF : CC₁ -->[ F ] CC₂)
               (GG : CC₁ -->[ G ] CC₂),
             FF ==>[ τ ] GG).
  Defined.

  Definition disp_prebicat_ops_on_cat_to_univ_cat
    : disp_prebicat_ops disp_prebicat_1_id_comp_cells_on_cat_to_univ_cat.
  Proof.
    repeat split.
    - intros C₁ C₂ F CC₁ CC₂ FF.
      exact (@disp_id2 _ D _ _ _ _ _ FF).
    - intros C₁ C₂ F CC₁ CC₂ FF.
      exact (@disp_lunitor _ D _ _ _ _ _ FF).
    - intros C₁ C₂ F CC₁ CC₂ FF.
      exact (@disp_runitor _ D _ _ _ _ _ FF).
    - intros C₁ C₂ F CC₁ CC₂ FF.
      exact (@disp_linvunitor _ D _ _ _ _ _ FF).
    - intros C₁ C₂ F CC₁ CC₂ FF.
      exact (@disp_rinvunitor _ D _ _ _ _ _ FF).
    - intros C₁ C₂ C₃ C₄ F G H CC₁ CC₂ CC₃ CC₄ FF GG HH.
      exact (@disp_rassociator _ D _ _ _ _ _ _ _ _ _ _ _ FF GG HH).
    - intros C₁ C₂ C₃ C₄ F G H CC₁ CC₂ CC₃ CC₄ FF GG HH.
      exact (@disp_lassociator _ D _ _ _ _ _ _ _ _ _ _ _ FF GG HH).
    - intros C₁ C₂ F G H τ θ CC₁ CC₂ FF GG HH ττ θθ.
      exact (@disp_vcomp2 _ D _ _ _ _ _ _ _ _ _ _ _ _ ττ θθ).
    - intros C₁ C₂ C₃ F G₁ G₂ τ CC₁ CC₂ CC₃ FF GG₁ GG₂ ττ.
      exact (@disp_lwhisker _ D _ _ _ _ _ _ _ _ _ _ FF _ _ ττ).
    - intros C₁ C₂ C₃ F₁ F₂ G τ CC₁ CC₂ CC₃ FF₁ FF₂ GG ττ.
      exact (@disp_rwhisker _ D _ _ _ _ _ _ _ _ _ _ _ _ GG ττ).
  Defined.

  Definition disp_prebicat_data_on_cat_to_univ_cat
    : disp_prebicat_data bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_1_id_comp_cells_on_cat_to_univ_cat.
    - exact disp_prebicat_ops_on_cat_to_univ_cat.
  Defined.

  Proposition disp_prebicat_laws_on_cat_to_univ_cat
    : disp_prebicat_laws disp_prebicat_data_on_cat_to_univ_cat.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - refine (disp_id2_left _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_id2_right _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vassocr _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_id2 _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_id2_rwhisker _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_vcomp _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_vcomp _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_lunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_runitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_lwhisker _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_lwhisker _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_rwhisker _ _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_whisker _ _ _ _ _ _ _ _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lunitor_linvunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_linvunitor_lunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_runitor_rinvunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rinvunitor_runitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lassociator_rassociator _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rassociator_lassociator _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_runitor_rwhisker _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lassociator_lassociator _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition disp_prebicat_on_cat_to_univ_cat
    : disp_prebicat bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_data_on_cat_to_univ_cat.
    - exact disp_prebicat_laws_on_cat_to_univ_cat.
  Defined.

  Definition disp_bicat_on_cat_to_univ_cat
    : disp_bicat bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_on_cat_to_univ_cat.
    - intros C₁ C₂ F G τ CC₁ CC₂ FF GG.
      apply (pr2 D).
  Defined.

  (**
   2. Properties of the reindexed displayed bicategory
   *)
  Proposition disp_2cells_isaprop_disp_bicat_on_cat_to_univ_cat
              (HD : disp_2cells_isaprop D)
    : disp_2cells_isaprop disp_bicat_on_cat_to_univ_cat.
  Proof.
    intros C₁ C₂ F G τ CC₁ CC₂ FF GG.
    apply HD.
  Qed.

  Proposition disp_2cells_iscontr_disp_bicat_on_cat_to_univ_cat
              (HD : disp_2cells_iscontr D)
    : disp_2cells_iscontr disp_bicat_on_cat_to_univ_cat.
  Proof.
    intros C₁ C₂ F G τ CC₁ CC₂ FF GG.
    apply HD.
  Qed.

  Proposition disp_locally_groupoid_bicat_on_cat_to_univ_cat
              (HD : disp_locally_groupoid D)
    : disp_locally_groupoid disp_bicat_on_cat_to_univ_cat.
  Proof.
    intros C₁ C₂ F G τ CC₁ CC₂ FF GG ττ.
    exact (HD (pr1 C₁) (pr1 C₂) F G τ CC₁ CC₂ FF GG ττ).
  Qed.

  Proposition disp_univalent_2_1_disp_bicat_on_cat_to_univ_cat
              (HD : disp_univalent_2_1 D)
    : disp_univalent_2_1 disp_bicat_on_cat_to_univ_cat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros C₁ C₂ F CC₁ CC₂ FF GG.
    use weqhomot.
    - refine (weqfibtototal
                _ _
                (λ τ,
                 weqfibtototal
                   _ _
                   (λ θ,
                    weqdirprodf
                      (weqimplimpl _ _ _ _)
                      (weqimplimpl _ _ _ _)))
              ∘ make_weq _ (HD (pr1 C₁) (pr1 C₂) F F (idpath F) CC₁ CC₂ FF GG))%weq.
      + abstract
          (intro p ;
           refine (p @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (intro p ;
           refine (p @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (apply (pr2 D)).
      + abstract
          (apply (pr2 D)).
      + abstract
          (intro p ;
           refine (p @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (intro p ;
           refine (p @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (apply (pr2 D)).
      + abstract
          (apply (pr2 D)).
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         apply idpath).
  Defined.

  (**
   3. The displayed pseudofunctor over the inclusion
   *)
  Definition disp_psfunctor_data_on_cat_to_univ_cat
    : disp_psfunctor_data
        disp_bicat_on_cat_to_univ_cat
        D
        univ_cats_to_cats.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ C CC, CC).
    - exact (λ C₁ C₂ F CC₁ CC₂ FF, FF).
    - exact (λ C₁ C₂ F G τ CC₁ CC₂ FF GG ττ, ττ).
    - exact (λ C CC, disp_id2_invertible_2cell (id_disp CC)).
    - exact (λ C₁ C₂ C₃ F G CC₁ CC₂ CC₃ FF GG, disp_id2_invertible_2cell (FF ;; GG)).
  Defined.

  Proposition is_disp_psfunctor_data_on_cat_to_univ_cat
              (HD : disp_2cells_isaprop D)
    : is_disp_psfunctor
        disp_bicat_on_cat_to_univ_cat
        D univ_cats_to_cats
        disp_psfunctor_data_on_cat_to_univ_cat.
  Proof.
    split7 ;
      intro ; intros ;
      apply (disp_2cells_isaprop_disp_bicat_on_cat_to_univ_cat HD).
  Qed.

  Definition disp_psfunctor_on_cat_to_univ_cat
             (HD : disp_2cells_isaprop D)
    : disp_psfunctor
        disp_bicat_on_cat_to_univ_cat
        D
        univ_cats_to_cats
    := disp_psfunctor_data_on_cat_to_univ_cat
       ,,
       is_disp_psfunctor_data_on_cat_to_univ_cat HD.
End DispBicatOnCats.
