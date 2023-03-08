(**********************************************************************

 Hom functor for enriched categories

 Enrichments can also be formulated using functors and natural
 transformations. In this file, we show that every enrichment gives
 rise to a hom functor, and that the identity and composition give rise
 to natural transformations.

 Note that formulating enrichments using functors and natural
 transformations have additional laws, which expresses the
 functoriality and the naturality of the hom-functor and the identity
 and composition. The laws for enrichments have the same formulation
 irregardless of whether we use a formulation with functors and
 transformations or as given in Enrichments.v.

 Contents
 1. The enriched hom functor
 2. The transformation that is pointwise the enriched identity
 3. The transformation that is pointwise the enriched composition

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section HomFunctor.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V).

  (**
   1. The enriched hom functor
   *)
  Definition enriched_hom_functor_data
    : functor_data (category_binproduct C^op C) V.
  Proof.
    use make_functor_data.
    - exact (λ x, E ⦃ pr1 x , pr2 x ⦄).
    - exact (λ x y f, precomp_arr E (pr2 x) (pr1 f) · postcomp_arr E (pr1 y) (pr2 f)).
  Defined.

  Definition enriched_hom_functor_laws
    : is_functor enriched_hom_functor_data.
  Proof.
    split.
    - intros x ; cbn.
      rewrite precomp_arr_id, postcomp_arr_id.
      apply id_left.
    - intros x y z f g ; cbn.
      rewrite precomp_arr_comp, postcomp_arr_comp ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply precomp_postcomp_arr.
  Qed.

  Definition enriched_hom_functor
    : category_binproduct C^op C ⟶ V.
  Proof.
    use make_functor.
    - exact enriched_hom_functor_data.
    - exact enriched_hom_functor_laws.
  Defined.

  (**
   2. The transformation that is pointwise the enriched identity
   *)
  Definition enriched_id_nat_trans_data
    : nat_trans_data
        (constant_functor (core C) V (I_{V}))
        (core_diag C ∙ enriched_hom_functor)
    := λ x, enriched_id E x.

  Definition enriched_id_nat_trans_laws
    : is_nat_trans
        _ _
        enriched_id_nat_trans_data.
  Proof.
    intros x y f ; unfold enriched_id_nat_trans_data ; cbn.
    rewrite id_left.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply enriched_id_precomp_arr.
    }
    etrans.
    {
      apply enriched_from_arr_postcomp.
    }
    etrans.
    {
      apply maponpaths.
      exact (z_iso_after_z_iso_inv f).
    }
    apply enriched_from_arr_id.
  Qed.

  Definition enriched_id_nat_trans
    : constant_functor _ V (I_{V}) ⟹ core_diag _ ∙ enriched_hom_functor.
  Proof.
    use make_nat_trans.
    - exact enriched_id_nat_trans_data.
    - exact enriched_id_nat_trans_laws.
  Defined.

  (**
   3. The transformation that is pointwise the enriched composition
   *)
  (*
  Definition enriched_comp_nat_trans_left_functor
    : category_binproduct (category_binproduct C^op (core C)) C ⟶ V
    := bindelta_pair_functor
         (bindelta_pair_functor
            (pr1_functor _ _ ∙ pr2_functor _ _ ∙ functor_core_op _)
            (pr2_functor _ _)
            ∙ enriched_hom_functor)
         (bindelta_pair_functor
            (pr1_functor _ _ ∙ pr1_functor _ _)
            (pr1_functor _ _ ∙ pr2_functor _ _ ∙ functor_core _)
          ∙ enriched_hom_functor)
       ∙ monoidal_cat_tensor _.

  Definition enriched_comp_nat_trans_right_functor
    : C^op ⊠ core C ⊠ C ⟶ V
    := bindelta_pair_functor
         (pr1_functor _ _ ∙ pr1_functor _ _)
         (pr2_functor _ _)
       ∙ enriched_hom_functor.

  Definition enriched_comp_nat_trans_data
    : nat_trans_data
        enriched_comp_nat_trans_left_functor
        enriched_comp_nat_trans_right_functor
    := λ x, enriched_comp E (pr11 x) (pr21 x) (pr2 x).

  Definition enriched_comp_nat_trans_laws
    : is_nat_trans _ _ enriched_comp_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    enough ((precomp_arr E (pr2 x) (inv_from_z_iso (pr21 f))
             · postcomp_arr E (pr21 y) (pr2 f))
            #⊗ (precomp_arr E (pr21 x) (pr11 f) · postcomp_arr E (pr11 y) (pr121 f))
            · enriched_comp_nat_trans_data y
            =
            enriched_comp_nat_trans_data x
            · precomp_arr E (pr2 x) (pr11 f)
            · postcomp_arr E (pr11 y) (pr2 f)) as X.
    {
      rewrite !assoc.
      exact X.
    }
    unfold enriched_comp_nat_trans_data.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply enriched_comp_precomp_arr.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply enriched_comp_postcomp_arr.
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (!(tensor_split _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply precomp_postcomp_arr.
      }
      apply tensor_comp_mor.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply tensor_split.
    }
    unfold precomp_arr.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply tensor_comp_id_r.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply enrichment_assoc.
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_id_r.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_lassociator.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (!(tensor_comp_id_l _ _)).
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply mon_inv_triangle.
    }
    etrans.
    {
      apply maponpaths.
      exact (!(tensor_comp_id_l _ _)).
    }
    refine (!(tensor_comp_id_l _ _) @ _).
    refine (_ @ tensor_id_id _ _).
    apply maponpaths.
    refine (_ @ !(postcomp_arr_comp E (pr121 f) (inv_from_z_iso (pr21 f))) @ _).
    - apply maponpaths.
      rewrite !assoc.
      apply idpath.
    - etrans.
      {
        apply maponpaths.
        exact (z_iso_inv_after_z_iso (pr21 f)).
      }
      apply postcomp_arr_id.
  Qed.

  Definition enriched_comp_nat_trans
    : enriched_comp_nat_trans_left_functor ⟹ enriched_comp_nat_trans_right_functor.
  Proof.
    use make_nat_trans.
    - exact enriched_comp_nat_trans_data.
    - exact enriched_comp_nat_trans_laws.
  Defined.
   *)
End HomFunctor.
