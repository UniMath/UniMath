(*******************************************************************

 The comprehension bicategory of functors into the category of strict categories

 Contents
 1. The comprehension pseudofunctor
 2. Preservation of cartesian cells
 3. The comprehension bicategory

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.IsosInTotal.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.IsOpfibration.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.IsPullback.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.Projection.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.Examples.FibrationsInStrictCats.
Require Import UniMath.Bicategories.Core.Examples.StrictCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FunctorsIntoCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FunctorsIntoCatCleaving.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

(**
 1. The comprehension pseudofunctor
 *)
Definition functors_into_cat_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_functors_into_cat
      (cod_disp_bicat bicat_of_strict_cats)
      (id_psfunctor bicat_of_strict_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C F,
           total_setcategory_of_set_functor F
           ,,
           pr1_total_category_of_set_functor F).
  - refine (λ C₁ C₂ F G₁ G₂ α, functor_total_category_of_set_functor F α ,, _).
    use make_invertible_2cell.
    + exact (functor_total_category_of_set_functor_comm F α).
    + apply is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_comm F α).
  - refine (λ C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂ p,
            nat_trans_total_category_of_set_functor α β₁ β₂ p
            ,,
            _).
    abstract
      (use nat_trans_eq ; [ apply C₂ | ] ;
       intro x ;
       cbn ;
       rewrite id_left, id_right ;
       apply idpath).
  - intros C F.
    simple refine (_ ,, _).
    + simple refine (_ ,, _).
      * exact (functor_total_category_of_set_functor_on_id F).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_on_id F).
  - intros C₁ C₂ C₃ F₁ F₂ G₁ G₂ G₃ α β.
    simple refine (_ ,, _).
    + simple refine (_ ,, _).
      * exact (functor_total_category_of_set_functor_on_comp α β).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ;
           cbn ;
           rewrite !id_left ;
           rewrite (functor_id F₂) ;
           rewrite !id_right ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_on_comp α β).
Defined.

Definition is_disp_psfunctor_functors_into_cat_comprehension
  : is_disp_psfunctor
      _ _ _
      functors_into_cat_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + apply idpath.
    + cbn.
      refine (_ @ !(id_left _)).
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + apply idpath.
    + cbn.
      refine (_ @ !(id_left _)).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 bb) (pr1 φ (pr1 x)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb (pr1 η (pr1 x)) (pr1 φ (pr1 x)))
                    (pr1 (pr1 ff (pr1 x)) (pr2 x)))).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb (pr1 η (pr1 x)) (pr1 φ (pr1 x)))
                    (pr1 (pr1 ff (pr1 x)) (pr2 x))
                  @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite !id_right ;
         rewrite functor_id ;
         apply idpath).
    + cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths.
                      refine (!_).
                      apply (pr1_maponpaths_idtoiso (pr1 ff (pr1 x))).
                    }
                    refine (!_).
                    apply (pr1_idtoiso_concat
                             (functor_total_category_of_set_functor_eq
                                f ff
                                (id₁ (pr1 x) ,, _))).
                  }
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp bb _ _) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id bb _) _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp bb _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber (functor_comp bb _ _) _ @ _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 ((eq_in_set_fiber (functor_comp bb _ _) _ @ _) @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite !id_right ;
         apply idpath).
    + cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         (eq_in_set_fiber
                            (functor_comp bb _ _)
                            _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (eq_in_set_fiber
                          (functor_id bb _)
                          _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber
                      (functor_comp bb _ _)
                      _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb _ _)
                    _
                  @ _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 ((eq_in_set_fiber (functor_comp bb _ _) _ @ _) @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite functor_id ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (eq_in_set_fiber
                          (functor_comp dd _ _)
                          _)).
            }
            refine (!_).
            exact (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber
                        (functor_id dd _)
                        _)).
          }
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp dd _ _)
                    _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp dd _ _)
                    _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (pr1 hh _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         _
                         (maponpaths
                            (pr11 (pr1 hh _))
                            (eq_in_set_fiber (functor_id cc _) _))).
              }
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         (eq_in_set_fiber (functor_comp dd _ _) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (eq_in_set_fiber (functor_comp dd _ _) _ @ _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp dd _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 (eq_in_set_fiber (functor_id dd _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 (_ @ eq_in_set_fiber (functor_id dd _) _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id cc _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat _ (_ @ eq_in_set_fiber (functor_id cc _) _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply (pr1_maponpaths_idtoiso (pr1 gg _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (functor_total_category_of_set_functor_eq
                          g gg
                          (nat_trans_total_category_of_set_functor_data
                             η ff₁ ff₂ ηη x))).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id cc _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat _ (_ @ eq_in_set_fiber (functor_id cc _) _)).
      }
      apply setcategory_eq_idtoiso.
Qed.

Definition functors_into_cat_comprehension
  : disp_psfunctor
      disp_bicat_of_functors_into_cat
      (cod_disp_bicat bicat_of_strict_cats)
      (id_psfunctor bicat_of_strict_cats)
  := functors_into_cat_comprehension_data
     ,,
     is_disp_psfunctor_functors_into_cat_comprehension.

(**
 2. Preservation of cartesian cells
 *)
Definition total_set_category_has_pb_ump
           {C₁ C₂ : setcategory}
           {F : C₁ ⟶ C₂}
           {G₁ : C₁ ⟶ cat_of_setcategory}
           {G₂ : C₂ ⟶ cat_of_setcategory}
           (α : G₁ ⟹ F ∙ G₂)
           (Hα : is_nat_z_iso α)
  : has_pb_ump
      (@make_pb_cone
         bicat_of_strict_cats
         C₁ (total_setcategory_of_set_functor G₂) C₂
         F (pr1_total_category_of_set_functor G₂)
         (total_setcategory_of_set_functor G₁)
         (pr1_total_category_of_set_functor G₁)
         (functor_total_category_of_set_functor F α)
         (make_invertible_2cell
            (is_invertible_2cell_bicat_of_strict_cat
               (functor_total_category_of_set_functor_comm F α)
               (is_nat_z_iso_functor_total_category_of_set_functor_comm F α)))).
Proof.
  split.
  - intro x.
    use make_pb_1cell.
    + apply (@total_set_category_pb_ump_1_mor
               _ _ _ _ _ _ Hα _
               (pb_cone_pr1 x) (pb_cone_pr2 x)
               (pr1 (pb_cone_cell x))).
      apply from_is_invertible_2cell_bicat_of_strict_cat.
      apply property_from_invertible_2cell.
    + use make_invertible_2cell.
      * apply (@total_set_category_pb_ump_1_mor_pr1
                 _ _ _ _ _ _ Hα _
                 (pb_cone_pr1 x) (pb_cone_pr2 x)
                 (pr1 (pb_cone_cell x))).
      * apply is_invertible_2cell_bicat_of_strict_cat.
        apply total_set_category_pb_ump_1_mor_pr1_is_nat_z_iso.
    + use make_invertible_2cell.
      * apply (@total_set_category_pb_ump_1_mor_pr2
                 _ _ _ _ _ _ Hα _
                 (pb_cone_pr1 x) (pb_cone_pr2 x)
                 (pr1 (pb_cone_cell x))).
      * apply is_invertible_2cell_bicat_of_strict_cat.
        apply total_set_category_pb_ump_1_mor_pr2_is_nat_z_iso.
    + abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro z ; cbn ;
         rewrite (functor_id F) ;
         rewrite !id_left, id_right ;
         exact (!(nat_trans_eq_pointwise (vcomp_rinv (pb_cone_cell x)) z))).
  - intros C₀ φ₁ φ₂ δ₁ δ₂ p.
    assert (∏ (x : pr1 C₀), pr1 (pr1 δ₂ x) = # F (pr1 δ₁ x)) as q.
    {
      abstract
        (intro x ;
         pose (nat_trans_eq_pointwise p x) as q ;
         cbn in q ;
         rewrite !id_left, !id_right in q ;
         exact q).
    }
    use iscontraprop1.
    + apply total_set_category_pb_ump_2_unique.
      apply Hα.
    + simple refine (_ ,, _ ,, _).
      * exact (total_set_category_pb_ump_2_cell _ Hα δ₁ δ₂ q).
      * apply total_set_category_pb_ump_2_pr1.
      * apply total_set_category_pb_ump_2_pr2.
Defined.

Definition local_opcartesian_functors_into_cat_comprehension
  : local_opcartesian_disp_psfunctor functors_into_cat_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂ p Hp.
  use is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
  use strict_pointwise_opcartesian_is_opcartesian.
  cbn.
  intro x.
  apply is_opcartesian_total_setcategory_of_set_functor.
  cbn.
  apply z_iso_is_z_isomorphism.
Qed.

Definition global_cartesian_functors_into_cat_comprehension
  : global_cartesian_disp_psfunctor functors_into_cat_comprehension.
Proof.
  intros C₁ C₂ F G₁ G₂ α Hα.
  use is_pb_to_cartesian_1cell.
  apply total_set_category_has_pb_ump.
  exact (functors_into_cat_cartesian_1cell_is_nat_iso _ Hα).
Defined.

(**
 3. The comprehension bicategory
 *)
Definition functors_into_cat_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_strict_cats
  := disp_bicat_of_functors_into_cat
     ,,
     functors_into_cat_comprehension
     ,,
     functors_into_cat_global_cleaving
     ,,
     global_cartesian_functors_into_cat_comprehension.

Definition is_covariant_functors_into_cat_comprehension_bicat
  : is_covariant functors_into_cat_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact functors_into_cat_local_opcleaving.
  - intro ; intros.
    apply functors_into_cat_is_opcartesian_2cell.
  - intro ; intros.
    apply functors_into_cat_is_opcartesian_2cell.
  - exact local_opcartesian_functors_into_cat_comprehension.
Defined.

Definition functors_into_cat_comprehension_bicat
  : comprehension_bicat
  := _
     ,,
     functors_into_cat_comprehension_bicat_structure
     ,,
     is_covariant_functors_into_cat_comprehension_bicat.
