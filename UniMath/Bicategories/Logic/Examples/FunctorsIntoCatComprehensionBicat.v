(*******************************************************************

 The comprehension bicategory of functors into categories

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


Definition TODO { A : UU } : A.
Admitted.









Section PullbackFromTotal.
  Context {C₁ C₂ : setcategory}
          {F : C₁ ⟶ C₂}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F ∙ G₂)
          (Hα : is_nat_z_iso α).

  Let αiso : nat_z_iso G₁ (F ∙ G₂) := α ,, Hα.
  Let αinv : F ∙ G₂ ⟹ G₁ := nat_z_iso_inv αiso.

  Local Lemma α_iso_α_inv
              (x : C₁)
              (y : pr1 (G₂ (F x)))
    : pr1 (α x) (pr1 (αinv x) y) = y.
  Proof.
    exact (maponpaths
             (λ z, pr11 z y)
             (z_iso_after_z_iso_inv
                (nat_z_iso_pointwise_z_iso αiso x))).
  Qed.

  Local Lemma α_iso_α_inv_on_mor
              (x : C₁)
              {y₁ y₂ : pr1 (G₂ (F x))}
              (f : y₁ --> y₂)
    : # (pr1 (α x)) (# (pr1 (αinv x)) f)
      =
      idtoiso (α_iso_α_inv x y₁)
      · f
      · idtoiso (!(α_iso_α_inv x y₂)).
  Proof.
    refine (from_eq_cat_of_setcategory
             (z_iso_after_z_iso_inv
                (nat_z_iso_pointwise_z_iso αiso x)) f @ _) ; cbn.
    apply setcategory_eq_idtoiso_comp.
  Qed.

  Local Lemma α_inv_α_iso
              (x : C₁)
              (y : pr1 (G₁ x))
    : pr1 (αinv x) (pr1 (α x) y) = y.
  Proof.
    exact (maponpaths
             (λ z, pr11 z y)
             (z_iso_inv_after_z_iso
                (nat_z_iso_pointwise_z_iso αiso x))).
  Qed.

  Local Lemma α_inv_α_iso_on_mor
              (x : C₁)
              {y₁ y₂ : pr1 (G₁ x)}
              (f : y₁ --> y₂)
    : # (pr1 (αinv x)) (# (pr1 (α x)) f)
      =
      idtoiso (α_inv_α_iso x y₁)
      · f
      · idtoiso (!(α_inv_α_iso x y₂)).
  Proof.
    refine (from_eq_cat_of_setcategory
              (z_iso_inv_after_z_iso
                 (nat_z_iso_pointwise_z_iso αiso x)) f @ _) ; cbn.
    apply setcategory_eq_idtoiso_comp.
  Qed.

  Section PbMor.
    Context {C₀ : setcategory}
            (P₁ : C₀ ⟶ C₁)
            (P₂ : C₀ ⟶ total_setcategory_of_set_functor G₂)
            (β : P₁ ∙ F ⟹ P₂ ∙ pr1_total_category_of_set_functor G₂)
            (Hβ : is_nat_z_iso β).

    Definition total_set_category_pb_ump_1_mor_eq
               {x y : C₀}
               (f : x --> y)
      : pr1 (# G₁ (# P₁ f)) ((pr11 (αinv (P₁ x))) ((pr11 (# G₂ (pr1 (Hβ x)))) (pr2 (P₂ x))))
        =
        pr1 (αinv (P₁ y)) (pr1 (# G₂ (pr1 (Hβ y))) (pr1 (# G₂ (pr1 (# P₂ f))) (pr2 (P₂ x)))).
    Proof.
      pose (maponpaths
              (λ z, pr11 z ((pr11 (# G₂ (pr1 (Hβ x)))) (pr2 (P₂ x))))
              (nat_trans_ax αinv _ _ (#P₁ f)))
        as p.
      cbn -[αinv] in p.
      refine (!p @ _).
      apply maponpaths.
      refine (maponpaths
                (λ z, pr11 z (pr2 (P₂ x)))
                (!(functor_comp G₂ (pr1 (Hβ x)) (# F (# P₁ f)))) @ _).
      refine (!(maponpaths
                  (λ z, pr1 (# G₂ z) (pr2 (P₂ x)))
                  (nat_trans_ax (nat_z_iso_inv (β ,, Hβ)) _ _ f)) @ _).
      exact (maponpaths
               (λ z, pr11 z (pr2 (P₂ x)))
               (functor_comp G₂ _ _)).
    Qed.

    Definition total_set_category_pb_ump_1_mor_data
      : functor_data
          C₀
          (total_setcategory_of_set_functor G₁).
    Proof.
      use make_functor_data.
      - refine (λ x, P₁ x ,, _).
        apply (αinv (P₁ x)).
        apply (# G₂ (pr1 (Hβ x))).
        exact (pr2 (P₂ x)).
      - refine (λ x y f,
                #P₁ f
                ,,
                _ · #(pr1 (αinv (P₁ y))) (# (pr1 (# G₂ (pr1 (Hβ y)))) (pr2 (# P₂ f)))).
        apply idtoiso.
        exact (total_set_category_pb_ump_1_mor_eq f).
    Defined.

    Definition total_set_category_pb_ump_1_mor_is_functor
      : is_functor total_set_category_pb_ump_1_mor_data.
    Proof.
      split.
      - intro x.
        use eq_mor_category_of_set_functor.
        + apply functor_id.
        + cbn -[αinv].
          etrans.
          {
            do 3 apply maponpaths.
            exact (eq_mor_category_of_set_functor_pr2 (functor_id P₂ x)).
          }
          cbn -[αinv].
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
                apply (pr1_idtoiso_concat
                         _
                         (eq_in_set_fiber (functor_id G₂ _) _)).
              }
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ x)))).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (αinv (P₁ x))).
          }
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq (id₁ x))).
          }
          refine (!_).
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber (functor_id G₁ (P₁ x)) _)).
          }
          apply setcategory_eq_idtoiso.
      - intros x y z f g.
        use eq_mor_category_of_set_functor.
        + apply functor_comp.
        + cbn -[αinv].
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                exact (eq_mor_category_of_set_functor_pr2 (functor_comp P₂ f g)).
              }
              refine (functor_comp _ _ _ @ _).
              apply maponpaths.
              apply functor_comp.
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths.
            apply functor_comp.
          }
          cbn -[αinv].
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ z)))).
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
          }
          refine (assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (Hβ z)))).
                }
                refine (!_).
                apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
              }
              refine (!_).
              apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq (f · g))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat (total_set_category_pb_ump_1_mor_eq (f · g) @ _)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₁ (# P₁ g))).
            }
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _)).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (_ @ eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _)).
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (from_eq_cat_of_setcategory
                     (!(nat_trans_ax αinv _ _ (# P₁ g)))
                     (# (pr1 (# G₂ (pr1 (Hβ y)))) (pr2 (# P₂ f)))).
          }
          etrans.
          {
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_idtoiso_concat
                     ((_ @ eq_in_set_fiber (functor_comp G₁ (# P₁ f) (# P₁ g)) _) @ _)).
          }
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_idtoiso_concat _ (total_set_category_pb_ump_1_mor_eq g)).
          }
          cbn -[αinv].
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              exact (from_eq_cat_of_setcategory
                       (!(functor_comp G₂ (pr1 (Hβ y)) (# F (# P₁ g))))
                       (pr2 (# P₂ f))).
            }
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            apply functor_comp.
          }
          etrans.
          {
            apply maponpaths_2.
            do 2 (refine (assoc _ _ _ @ _) ; apply maponpaths_2).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (((_ @ eq_in_set_fiber (functor_comp G₁ _ _) _) @ _) @ _)).
          }
          do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     _
                     (_ @ total_set_category_pb_ump_1_mor_eq g)).
          }
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply maponpaths.
            exact (from_eq_cat_of_setcategory
                     (maponpaths
                        (λ q, # G₂ q)
                        (!(nat_trans_ax (nat_z_iso_inv (β ,, Hβ)) _ _ g)))
                     (pr2 (# P₂ f))).
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              apply functor_comp.
            }
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     _
                     (_ @ _ @ total_set_category_pb_ump_1_mor_eq g)).
          }
          cbn -[αinv].
          refine (assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     ((((_ @ eq_in_set_fiber (functor_comp G₁ _ _) _) @ _) @ _) @ _)).
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply maponpaths.
            exact (from_eq_cat_of_setcategory
                       (functor_comp G₂ _ _) _).
          }
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              refine (functor_comp _ _ _ @ _).
              apply maponpaths_2.
              apply functor_comp.
            }
            do 2 refine (assoc' _ _ _ @ _).
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                refine (!_).
                apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (_ @ _ @ _ @ total_set_category_pb_ump_1_mor_eq g)).
            }
            etrans.
            {
              apply maponpaths.
              apply setcategory_refl_idtoiso.
            }
            apply id_right.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (αinv (P₁ z))).
          }
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (((((_ @ eq_in_set_fiber (functor_comp G₁ _ _) _) @ _) @ _) @ _) @ _)).
          }
          apply setcategory_eq_idtoiso.
    Time Qed.

    Definition total_set_category_pb_ump_1_mor
      : C₀ ⟶ total_setcategory_of_set_functor G₁.
    Proof.
      use make_functor.
      - exact total_set_category_pb_ump_1_mor_data.
      - exact total_set_category_pb_ump_1_mor_is_functor.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr1
      : total_set_category_pb_ump_1_mor ∙ pr1_total_category_of_set_functor G₁
        ⟹
        P₁.
    Proof.
      use make_nat_trans.
      - exact (λ _, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr2_eq
               (x : C₀)
      : pr1 (# G₂ (β x))
          (pr1 (pr1 α (P₁ x))
             ((pr11 (αinv (P₁ x)))
                ((pr11 (# G₂ (pr1 (Hβ x))))
                   (pr2 (P₂ x)))))
        =
        pr2 (P₂ x).
    Proof.
      etrans.
      {
        apply maponpaths.
        apply α_iso_α_inv.
      }
      etrans.
      {
        exact (maponpaths
                 (λ z, pr11 z (pr2 (P₂ x)))
                 (!(functor_comp G₂ (pr1 (Hβ x)) (β x)))).
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        exact (z_iso_after_z_iso_inv (_ ,, Hβ x)).
      }
      cbn.
      etrans.
      {
        exact (maponpaths
                 (λ z, pr11 z (pr2 (P₂ x)))
                 (functor_id G₂ _)).
      }
      cbn.
      apply idpath.
    Qed.

    Definition total_set_category_pb_ump_1_mor_pr2_data
      : nat_trans_data
          (total_set_category_pb_ump_1_mor ∙ functor_total_category_of_set_functor F α)
          P₂.
    Proof.
      refine (λ x, β x ,, _).
      refine (idtoiso _).
      apply total_set_category_pb_ump_1_mor_pr2_eq.
    Defined.

    Definition total_set_category_pb_ump_1_mor_pr2_is_nat_trans
      : is_nat_trans
          _ _
          total_set_category_pb_ump_1_mor_pr2_data.
    Proof.
      intros x y f.
      use eq_mor_category_of_set_functor.
      - apply (nat_trans_ax β).
      - cbn -[αinv].
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
                refine (functor_comp _ _ _ @ _).
                etrans.
                {
                  apply maponpaths_2.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (α (P₁ y))).
                }
                etrans.
                {
                  apply maponpaths.
                  apply α_iso_α_inv_on_mor.
                }
                refine (assoc _ _ _ @ _).
                apply maponpaths_2.
                refine (assoc _ _ _ @ _).
                apply maponpaths_2.
                refine (!_).
                apply (pr1_idtoiso_concat
                         (maponpaths
                            (pr11 (α (P₁ y)))
                            (total_set_category_pb_ump_1_mor_eq f))).
              }
              refine (assoc _ _ _ @ _).
              apply maponpaths_2.
              refine (assoc _ _ _ @ _).
              apply maponpaths_2.
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (maponpaths
                          (pr11 (α (P₁ y)))
                          (total_set_category_pb_ump_1_mor_eq f) @ _)).
            }
            refine (functor_comp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (β y))).
            }
            apply maponpaths_2.
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₂ (β y))).
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp G₂ _ _) _)).
        }
        do 2 refine (assoc' _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (total_set_category_pb_ump_1_mor_pr2_eq y)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (from_eq_cat_of_setcategory
                   ((!functor_comp G₂ (pr1 (Hβ y)) (β y))
                    @ maponpaths
                        (λ z, # G₂ z)
                        (z_iso_after_z_iso_inv (_ ,, Hβ y))
                    @ functor_id G₂ _)
                   (pr2 (# P₂ f))).
        }
        etrans.
        {
          apply maponpaths.
          do 2 refine (assoc' _ _ _ @ _).
          do 2 apply maponpaths.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (_ @ total_set_category_pb_ump_1_mor_pr2_eq y)).
        }
        do 2 refine (assoc _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp G₂ _ _) _ @ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply setcategory_refl_idtoiso.
        }
        refine (id_right _ @ _).
        refine (_ @ assoc' _ _ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (# G₂ (pr1 (# P₂ f)))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (eq_in_set_fiber (functor_comp G₂ _ _) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G₂ _ _) _ @ _)).
        }
        apply setcategory_eq_idtoiso.
    Qed.

    Definition total_set_category_pb_ump_1_mor_pr2
      : total_set_category_pb_ump_1_mor ∙ functor_total_category_of_set_functor F α
        ⟹
        P₂.
    Proof.
      use make_nat_trans.
      - exact total_set_category_pb_ump_1_mor_pr2_data.
      - exact total_set_category_pb_ump_1_mor_pr2_is_nat_trans.
    Defined.
  End PbMor.

  Section PbCell.
    Context {C₀ : setcategory}
            {φ₁ φ₂ : pr1 C₀ ⟶ total_setcategory_of_set_functor G₁}
            (δ₁ : φ₁ ∙ pr1_total_category_of_set_functor G₁
                  ⟹
                  φ₂ ∙ pr1_total_category_of_set_functor G₁)
            (δ₂ : φ₁ ∙ functor_total_category_of_set_functor F α
                  ⟹
                  φ₂ ∙ functor_total_category_of_set_functor F α)
            (q : ∏ (x : C₀), pr1 (δ₂ x) = # F (δ₁ x)).

    Definition total_set_category_pb_ump_2_unique
      : isaprop
          (∑ (γ : φ₁ ⟹ φ₂),
            post_whisker γ (pr1_total_category_of_set_functor G₁) = δ₁
            ×
            post_whisker γ (functor_total_category_of_set_functor F α) = δ₂).
    Proof.
      use invproofirrelevance.
      intros ζ ξ.
      use subtypePath.
      {
        intro.
        use isapropdirprod ; apply isaset_nat_trans ; apply homset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use eq_mor_category_of_set_functor.
      - exact (nat_trans_eq_pointwise (pr12 ζ) x @ !(nat_trans_eq_pointwise (pr12 ξ) x)).
      - assert (p := maponpaths
                       (λ z, #(pr1 (αinv (pr1 (φ₂ x)))) z)
                       (eq_mor_category_of_set_functor_pr2
                          (nat_trans_eq_pointwise (pr22 ζ) x
                           @ !(nat_trans_eq_pointwise (pr22 ξ) x)))).
        cbn -[αinv] in p.
        rewrite !(functor_comp (αinv (pr1 (φ₂ x)))) in p.
        rewrite !α_inv_α_iso_on_mor in p.
        (*
        simple refine (_ @ maponpaths (λ z, idtoiso TODO · z · idtoiso TODO) p @ _).
         *)
        Check  p.
        apply TODO.
    Qed.

    Definition total_set_category_pb_ump_2_cell_data
      : nat_trans_data φ₁ φ₂.
    Proof.
      refine (λ x, δ₁ x ,, _).
      refine (idtoiso _ · # (pr1 (αinv (pr1 (φ₂ x)))) (pr2 (δ₂ x)) · idtoiso _).
      - abstract
          (rewrite q ;
           cbn -[αinv] ;
           pose (maponpaths (λ z, pr11 z (pr2 (φ₁ x))) (nat_trans_ax α _ _ (δ₁ x))) as p ;
           cbn in p ;
           refine (!_) ;
           etrans ;
             [ apply maponpaths ;
               exact (!p)
             | ] ;
           apply α_inv_α_iso).
      - abstract
          (apply α_inv_α_iso).
    Defined.

    Definition total_set_category_pb_ump_2_cell_is_nat_trans
      : is_nat_trans φ₁ φ₂ total_set_category_pb_ump_2_cell_data.
    Proof.
      intros x y f.
      use eq_mor_category_of_set_functor.
      - exact (nat_trans_ax δ₁ _ _ f).
      - cbn -[αinv].
        refine (!_).
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G₁ _ _) _)).
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (functor_comp _ _ _ @ _).
            apply maponpaths_2.
            apply functor_comp.
          }
          rewrite !assoc.
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₁ (pr1 (# φ₂ f)))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (_ @ eq_in_set_fiber (functor_comp G₁ _ _) _)).
        }


        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (from_eq_cat_of_setcategory
                   (!(nat_trans_ax αinv _ _ (pr1 (# φ₂ f))))
                   (pr2 (δ₂ x))).
        }
        cbn -[αinv].

        pose (maponpaths
                (λ z, # (pr1 (αinv (pr1 (φ₂ y)))) z)
                (eq_mor_category_of_set_functor_pr2
                   (nat_trans_ax δ₂ _ _ f)))
          as p.
    Admitted.

    Definition total_set_category_pb_ump_2_cell
      : φ₁ ⟹ φ₂.
    Proof.
      use make_nat_trans.
      - exact total_set_category_pb_ump_2_cell_data.
      - exact total_set_category_pb_ump_2_cell_is_nat_trans.
    Defined.

    Definition total_set_category_pb_ump_2_pr1
      : post_whisker
          total_set_category_pb_ump_2_cell
          (pr1_total_category_of_set_functor G₁)
        =
        δ₁.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    Qed.

    Definition total_set_category_pb_ump_2_pr2
      : post_whisker
          total_set_category_pb_ump_2_cell
          (functor_total_category_of_set_functor F α)
        =
        δ₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use eq_mor_category_of_set_functor.
      - cbn.
        exact (!(q x)).
      - cbn -[αinv].
        etrans.
        {
          apply maponpaths.
          refine (functor_comp _ _ _ @ _).
          apply maponpaths_2.
          refine (functor_comp _ _ _ @ _).
          apply maponpaths.
          apply α_iso_α_inv_on_mor.
        }
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (α (pr1 (φ₂ x)))).
          }
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (pr1_maponpaths_idtoiso (α (pr1 (φ₂ x)))).
            }
            refine (!_).
            apply (pr1_idtoiso_concat
                     (functor_total_category_of_set_functor_eq
                        F α
                        (total_set_category_pb_ump_2_cell_data x))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (functor_total_category_of_set_functor_eq
                      F α
                      (total_set_category_pb_ump_2_cell_data x) @ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply setcategory_refl_idtoiso.
        }
        refine (id_right _ @ _).
        apply maponpaths_2.
        apply setcategory_eq_idtoiso.
    Time Qed.
  End PbCell.

  Definition total_set_category_has_pb_ump
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
      + apply (total_set_category_pb_ump_1_mor
                 (pb_cone_pr1 x) (pb_cone_pr2 x)
                 (pr1 (pb_cone_cell x))).
        apply from_is_invertible_2cell_bicat_of_strict_cat.
        apply property_from_invertible_2cell.
      + use make_invertible_2cell.
        * apply (total_set_category_pb_ump_1_mor_pr1
                   (pb_cone_pr1 x) (pb_cone_pr2 x)
                   (pr1 (pb_cone_cell x))).
        * apply is_invertible_2cell_bicat_of_strict_cat.
          intro ; cbn.
          apply is_z_isomorphism_identity.
      + use make_invertible_2cell.
        * apply (total_set_category_pb_ump_1_mor_pr2
                   (pb_cone_pr1 x) (pb_cone_pr2 x)
                   (pr1 (pb_cone_cell x))).
        * apply is_invertible_2cell_bicat_of_strict_cat.
          (*intro ; cbn.
          use is_z_iso_total_setcategory_of_set_functor.
          ** cbn.
             apply TODO.
          ** cbn.
          cbn.*)
          apply TODO.
      + (*
        use nat_trans_eq ; [ apply homset_property | ].
        intro z ; cbn.
        rewrite (functor_id F).
        rewrite !id_left, id_right.
        *)
        apply TODO.
    - intros C₀ φ₁ φ₂ δ₁ δ₂ p.
      assert (∏ (x : pr1 C₀), pr1 (pr1 δ₂ x) = # F (pr1 δ₁ x)) as q.
      {
        intro x.
        pose (nat_trans_eq_pointwise p x) as q.
        cbn in q .
        rewrite !id_left, !id_right in q.
        exact q.
      }
      use iscontraprop1.
      + apply total_set_category_pb_ump_2_unique.
      + simple refine (_ ,, _ ,, _).
        * exact (total_set_category_pb_ump_2_cell δ₁ δ₂ q).
        * apply total_set_category_pb_ump_2_pr1.
        * apply total_set_category_pb_ump_2_pr2.
  Defined.
End PullbackFromTotal.

Definition global_cartesian_functors_into_cat_comprehension
  : global_cartesian_disp_psfunctor functors_into_cat_comprehension.
Proof.
  intros C₁ C₂ F G₁ G₂ α Hα.
  use is_pb_to_cartesian_1cell.
  apply total_set_category_has_pb_ump.
  exact (functors_into_cat_cartesian_1cell_is_nat_iso _ Hα).
Defined.

(************************************************


    ∫ G₁ ⟶ ∫ G₂
      |       |
      V       V
      C₁ ⟶   C₂

 is a pb

 ************************************************)


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
