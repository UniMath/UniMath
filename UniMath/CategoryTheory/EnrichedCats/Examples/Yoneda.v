(**********************************************************************

 The Yoneda embedding for enriched categories

 In this file, we define the Yoneda embedding for enriched categories.
 To do so, we first define representable presheaves and representable
 natural transformations.

 There are a couple of things to notice about this construction, First
 of all, to guarantee that the presheaf category is enriched, we need
 to assume that the monoidal category over which we enrich, is symmetric
 and closed, and that we have enough limits, namely equalizers and
 products indexed over the objects of `C` (for this, we must assume
 that `C` is sufficiently small compared to `V`). Second of all, since
 the presheaves land in the monoidal category `V`, most of the
 construction is manipulating the function spaces of `V`.

 Contents
 1. Representable presheaves
 2. Representable natural transformations
 3. The enriched Yoneda embedding

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section YonedaEmbedding.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (EqV : Equalizers V)
          (PV : Products C V)
          (PV' : Products (C × C) V).

  (**
   1. Representable presheaves
   *)
  Section RepresentablePresheaf.
    Context (y : C).

    Definition enriched_repr_presheaf_data
      : functor_data (C ^opp) V.
    Proof.
      use make_functor_data.
      - exact (λ x, E ⦃ x , y ⦄).
      - exact (λ x₁ x₂ f, precomp_arr E y f).
    Defined.

    Proposition is_functor_enriched_repr_presheaf
      : is_functor enriched_repr_presheaf_data.
    Proof.
      split.
      - intros x ; cbn.
        rewrite precomp_arr_id.
        apply idpath.
      - intros x₁ x₂ x₃ f₁ f₂ ; cbn.
        rewrite precomp_arr_comp.
        apply idpath.
    Qed.

    Definition enriched_repr_presheaf_functor
      : C^opp ⟶ V.
    Proof.
      use make_functor.
      - exact enriched_repr_presheaf_data.
      - exact is_functor_enriched_repr_presheaf.
    Defined.

    Definition enriched_repr_presheaf_enrichment_data
      : functor_enrichment_data
          enriched_repr_presheaf_functor
          (op_enrichment V E)
          (self_enrichment V)
      := λ x₁ x₂, internal_lam (sym_mon_braiding _ _ _ · enriched_comp E x₂ x₁ y).

    Arguments enriched_repr_presheaf_enrichment_data /.

    Proposition enriched_repr_presheaf_enrichment_laws
      : is_functor_enrichment enriched_repr_presheaf_enrichment_data.
    Proof.
      repeat split.
      - intro x ; cbn -[sym_mon_braiding].
        use internal_funext.
        intros a h.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_split.
        }
        rewrite !assoc'.
        unfold internal_id.
        rewrite internal_beta.
        refine (!_).
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        apply sym_mon_braiding_runitor.
      - intros x₁ x₂ x₃ ; cbn -[sym_mon_braiding].
        use internal_funext.
        intros a h.
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite !internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            rewrite <- tensor_comp_mor.
            rewrite id_right.
            apply maponpaths.
            rewrite tensor_split.
            rewrite !assoc'.
            rewrite internal_beta.
            apply idpath.
          }
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !tensor_comp_id_r.
          rewrite !assoc'.
          apply idpath.
        }
        rewrite enrichment_assoc.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite sym_mon_tensor_lassociator.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          rewrite tensor_split'.
          apply idpath.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_rassociator.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite <- tensor_sym_mon_braiding.
          rewrite tensor_comp_id_l.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_lassociator.
        rewrite tensor_id_id.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- sym_mon_hexagon_rassociator.
          rewrite !assoc'.
          rewrite mon_rassociator_lassociator.
          rewrite id_right.
          apply idpath.
        }
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        apply id_left.
      - intros x₁ x₂ f ; cbn -[sym_mon_braiding].
        use internal_funext.
        intros a h.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_from_arr.
        rewrite internal_beta.
        unfold precomp_arr.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(id_right _) @ _).
        rewrite <- mon_runitor_rinvunitor.
        rewrite !assoc.
        apply maponpaths_2.
        apply sym_mon_braiding_runitor.
    Qed.

    Definition enriched_repr_presheaf_enrichment
      : functor_enrichment
          enriched_repr_presheaf_functor
          (op_enrichment V E)
          (self_enrichment V)
      := enriched_repr_presheaf_enrichment_data
         ,,
         enriched_repr_presheaf_enrichment_laws.

    Definition enriched_repr_presheaf
      : enriched_functor_category
          (op_enrichment V E)
          (self_enrichment V).
    Proof.
      simple refine (_ ,, _).
      - exact enriched_repr_presheaf_functor.
      - exact enriched_repr_presheaf_enrichment.
    Defined.
  End RepresentablePresheaf.

  Arguments enriched_repr_presheaf_enrichment_data /.

  (**
   2. Representable natural transformations
   *)
  Section RepresentableTransformation.
    Context {y₁ y₂ : C}
            (g : y₁ --> y₂).

    Definition enriched_repr_nat_trans_mor
      : enriched_repr_presheaf_functor y₁
        ⟹
        enriched_repr_presheaf_functor y₂.
    Proof.
      use make_nat_trans.
      - exact (λ x, postcomp_arr E x g).
      - abstract
          (intros x₁ x₂ f ; cbn ;
           rewrite precomp_postcomp_arr ;
           apply idpath).
    Defined.

    Proposition enriched_repr_nat_trans_enrichment
      : nat_trans_enrichment
          enriched_repr_nat_trans_mor
          (enriched_repr_presheaf_enrichment y₁)
          (enriched_repr_presheaf_enrichment y₂).
    Proof.
      use nat_trans_enrichment_via_comp.
      intros x₁ x₂ ; cbn -[sym_mon_braiding].
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite self_enrichment_precomp.
      rewrite internal_beta.
      rewrite self_enrichment_postcomp.
      rewrite internal_beta.
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite enriched_comp_postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc.
      rewrite tensor_comp_id_l.
      apply idpath.
    Qed.

    Definition enriched_repr_nat_trans
      : enriched_repr_presheaf y₁ --> enriched_repr_presheaf y₂
      := enriched_repr_nat_trans_mor ,, enriched_repr_nat_trans_enrichment.
  End RepresentableTransformation.

  (**
   3. The enriched Yoneda embedding
   *)
  Definition enriched_yoneda_data
    : functor_data
        C
        (enriched_functor_category
           (op_enrichment V E)
           (self_enrichment V)).
  Proof.
    use make_functor_data.
    - exact (λ y, enriched_repr_presheaf y).
    - exact (λ y₁ y₂ g, enriched_repr_nat_trans g).
  Defined.

  Proposition is_functor_enriched_yoneda
    : is_functor enriched_yoneda_data.
  Proof.
    split.
    - intros y.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq ; [ apply homset_property | ].
      intros x ; cbn.
      apply postcomp_arr_id.
    - intros y₁ y₂ y₃ g₁ g₂.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq ; [ apply homset_property | ].
      intros x ; cbn.
      apply postcomp_arr_comp.
  Qed.

  Definition enriched_yoneda_functor
    : C
      ⟶
      enriched_functor_category
        (op_enrichment V E)
        (self_enrichment V).
  Proof.
    use make_functor.
    - exact enriched_yoneda_data.
    - exact is_functor_enriched_yoneda.
  Defined.

  Definition enriched_yoneda_enrichment_data_ob
             (y₁ y₂ : C)
    : E ⦃ y₁, y₂ ⦄ --> PV (λ x, (E ⦃ x, y₁ ⦄) ⊸ (E ⦃ x, y₂ ⦄))
    := ProductArrow _ _ _ (λ x, internal_lam (enriched_comp E x y₁ y₂)).

  Arguments enriched_yoneda_enrichment_data_ob /.

  Proposition enriched_yoneda_enrichment_data_eq
              (y₁ y₂ : C)
    : enriched_yoneda_enrichment_data_ob y₁ y₂
      · @enriched_functor_left_map
           V (C^opp)
           _ _ _ _
           PV'
           (enriched_repr_presheaf_functor y₁)
           _
           (enriched_repr_presheaf_enrichment y₂)
      =
      enriched_yoneda_enrichment_data_ob y₁ y₂
      · enriched_functor_right_map _ _ _ _ (enriched_repr_presheaf_enrichment y₁).
  Proof.
    use ProductArrow_eq.
    intros x.
    unfold enriched_functor_left_map, enriched_functor_right_map.
    rewrite !assoc'.
    refine (maponpaths (λ z, _ · z) (ProductPrCommutes (C × C) V _ _ _ _ _) @ _).
    refine (_ @ !(maponpaths (λ z, _ · z) (ProductPrCommutes (C × C) V _ _ _ _ _))).
    rewrite !assoc.
    cbn.
    refine (maponpaths (λ z, z · _) (ProductPrCommutes C V _ _ _ _ _) @ _).
    refine (_ @ !(maponpaths (λ z, z · _) (ProductPrCommutes C V _ _ _ _ _))).
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob.
    rewrite !assoc'.
    rewrite !internal_beta.
    cbn -[sym_mon_braiding].
    use internal_funext.
    intros a' h'.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite !internal_beta.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_id_id.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_mor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite internal_beta.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite internal_beta.
      apply idpath.
    }
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !tensor_comp_id_l.
    rewrite !assoc'.
    rewrite enrichment_assoc'.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite tensor_sym_mon_braiding.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply tensor_split.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_comp_mor.
      rewrite id_left, id_right.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_rassociator.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    refine (_ @ id_right _).
    rewrite <- mon_lassociator_rassociator.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply sym_mon_hexagon_lassociator.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_inv.
    rewrite tensor_id_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition enriched_yoneda_enrichment_data
    : functor_enrichment_data
        enriched_yoneda_functor
        E
        (enriched_presheaf_enrichment E EqV PV PV').
  Proof.
    intros y₁ y₂.
    refine (EqualizerIn _ _ (enriched_yoneda_enrichment_data_ob y₁ y₂) _).
    exact (enriched_yoneda_enrichment_data_eq y₁ y₂).
  Defined.

  Arguments enriched_yoneda_enrichment_data /.

  Proposition is_functor_enrichment_enriched_yoneda
    : is_functor_enrichment enriched_yoneda_enrichment_data.
  Proof.
    repeat split.
    - intros x ; cbn.
      use EqualizerInsEq.
      rewrite !assoc'.
      unfold enriched_functor_hom_id, mor_to_enriched_functor_hom.
      rewrite !EqualizerCommutes.
      use ProductArrow_eq.
      intro y.
      rewrite !assoc'.
      cbn.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      refine (_ @ !(ProductPrCommutes C V _ _ _ _ _)).
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_id.
      rewrite internal_beta.
      rewrite enrichment_id_left.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    - intros x y z ; cbn.
      use EqualizerInsEq.
      rewrite !assoc'.
      unfold enriched_functor_hom_comp, mor_to_enriched_functor_hom.
      rewrite !EqualizerCommutes.
      use ProductArrow_eq.
      intro w.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      unfold enriched_functor_hom_comp_data, enriched_functor_hom_pr.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite !assoc.
      rewrite !EqualizerCommutes.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (ProductPrCommutes C V _ _ _ _ _).
        }
        apply maponpaths_2.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      refine (!_).
      use internal_funext ; cbn.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite !internal_beta.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply maponpaths_2.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite enrichment_assoc.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_comp_id_l.
      apply idpath.
    - intros x y f ; cbn.
      use EqualizerInsEq.
      rewrite !assoc'.
      unfold enriched_functor_hom_from_arr, mor_to_enriched_functor_hom.
      rewrite !EqualizerCommutes.
      use ProductArrow_eq.
      intro z.
      rewrite !assoc'.
      cbn.
      refine (ProductPrCommutes C V _ _ _ _ _ @ !_).
      etrans.
      {
        apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite internal_beta.
      unfold postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lunitor_linvunitor.
        apply id_left.
      }
      rewrite <- tensor_split.
      apply idpath.
  Qed.

  Definition enriched_yoneda_enrichment
    : functor_enrichment
        enriched_yoneda_functor
        E
        (enriched_presheaf_enrichment E EqV PV PV')
    := enriched_yoneda_enrichment_data
       ,,
       is_functor_enrichment_enriched_yoneda.

  Definition enriched_yoneda
    : enriched_functor_category
        E
        (enriched_presheaf_enrichment E EqV PV PV')
    := enriched_yoneda_functor
       ,,
       enriched_yoneda_enrichment.
End YonedaEmbedding.

Arguments enriched_repr_presheaf_enrichment_data /.
Arguments enriched_yoneda_enrichment_data_ob /.
Arguments enriched_yoneda_enrichment_data /.
