Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section EnrichedMors.
  Context (V : monoidal_cat)
          (C : enriched_precat V).

  Definition underlying_precategory_ob_mor_enriched
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, I_{V} --> enriched_cat_mor x y).
  Defined.

  Definition underlying_precategory_data_enriched
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact underlying_precategory_ob_mor_enriched.
    - exact (λ x , enriched_cat_identity x).
    - exact (λ x y z f g, mon_linvunitor _ · g #⊗ f · enriched_cat_comp x y z).
  Defined.

  Definition underlying_precategory_enriched_laws
    : is_precategory underlying_precategory_data_enriched.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split.
    - cbn ; intros x y f.
      rewrite !assoc'.
      rewrite tensor_split'.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (enriched_id_right x y : _ = mon_runitor _).
      }
      rewrite tensor_runitor.
      rewrite mon_runitor_I_mon_lunitor_I.
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (mon_linvunitor_lunitor _).
      }
      apply id_left.
    - cbn ; intros x y f.
      rewrite !assoc'.
      rewrite tensor_split.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (enriched_id_left x y : _ = mon_lunitor _).
      }
      rewrite tensor_lunitor.
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (mon_linvunitor_lunitor _).
      }
      apply id_left.
    - cbn ; intros w x y z f g h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (enriched_assoc w x y z : (_ #⊗ _) · _
                                        =
                                        mon_lassociator _ _ _ · ((_ #⊗ _) · _)).
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply tensor_lassociator.
      }
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_right.
      rewrite !tensor_comp_l_id_l.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!(tensor_linvunitor (mon_linvunitor _))).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply mon_linvunitor_triangle.
      }
      rewrite !assoc'.
      rewrite <- tensor_lassociator.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      apply tensor_lassociator.
  Qed.

  Definition underlying_precategory_enriched
    : precategory.
  Proof.
    use make_precategory.
    - exact underlying_precategory_data_enriched.
    - exact underlying_precategory_enriched_laws.
  Defined.

  Definition underlying_category_enriched
    : category.
  Proof.
    use make_category.
    - exact underlying_precategory_enriched.
    - intros x y.
      apply homset_property.
  Defined.

  Definition enrichment_data_of_underlying_category
    : enrichment_data underlying_category_enriched V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, enriched_cat_mor x y).
    - exact (λ x , enriched_cat_identity x).
    - exact (λ x y z, enriched_cat_comp x y z).
    - exact (λ x y f, f).
    - exact (λ x y f, f).
  Defined.

  Definition enrichment_laws_of_underlying_category
    : enrichment_laws enrichment_data_of_underlying_category.
  Proof.
    repeat split ; cbn ; intros.
    - refine (!_).
      apply C.
    - refine (!_).
      apply C.
    - rewrite !assoc'.
      apply C.
  Qed.

  Definition enrichment_of_underlying_category
    : enrichment underlying_category_enriched V.
  Proof.
    simple refine (_ ,, _).
    - exact enrichment_data_of_underlying_category.
    - exact enrichment_laws_of_underlying_category.
  Defined.

  Definition underlying_cat_with_enrichment
    : cat_with_enrichment V
    := underlying_category_enriched
       ,,
       enrichment_of_underlying_category.
End EnrichedMors.
