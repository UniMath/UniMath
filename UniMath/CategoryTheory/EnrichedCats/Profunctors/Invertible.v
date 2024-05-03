(******************************************************************************************


 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section InvertibleTransformation.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {P Q : E₁ ↛e E₂}
          (τ : enriched_profunctor_transformation P Q).

  Definition is_iso_enriched_profunctor_transformation
    : UU
    := ∏ (y : C₂) (x : C₁), is_z_isomorphism (τ y x).

  Definition pointwise_iso_enriched_profunctor_transformation
             (Hτ : is_iso_enriched_profunctor_transformation)
             (y : C₂)
             (x : C₁)
    : z_iso (P y x) (Q y x)
    := _ ,, Hτ y x.

  Definition pointwise_inv_enriched_profunctor_transformation
             (Hτ : is_iso_enriched_profunctor_transformation)
             (y : C₂)
             (x : C₁)
    : Q y x --> P y x
    := inv_from_z_iso (pointwise_iso_enriched_profunctor_transformation Hτ y x).

  Section Inverse.
    Context (Hτ : is_iso_enriched_profunctor_transformation).

    Proposition inv_enriched_profunctor_transformation_laws
      : enriched_profunctor_transformation_laws
          (pointwise_inv_enriched_profunctor_transformation Hτ).
    Proof.
      split.
      - intros y₁ y₂ x ; cbn.
        unfold pointwise_inv_enriched_profunctor_transformation.
        use z_iso_inv_on_left ; cbn.
        rewrite !assoc'.
        rewrite <- enriched_profunctor_transformation_lmap_e.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite z_iso_after_z_iso_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      - intros y x₁ x₂ ; cbn.
        unfold pointwise_inv_enriched_profunctor_transformation.
        use z_iso_inv_on_left ; cbn.
        rewrite !assoc'.
        rewrite <- enriched_profunctor_transformation_rmap_e.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite z_iso_after_z_iso_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition inv_enriched_profunctor_transformation
      : enriched_profunctor_transformation Q P.
    Proof.
      use make_enriched_profunctor_transformation.
      - exact (pointwise_inv_enriched_profunctor_transformation Hτ).
      - exact inv_enriched_profunctor_transformation_laws.
    Defined.
  End Inverse.
End InvertibleTransformation.

Arguments pointwise_inv_enriched_profunctor_transformation {V C₁ C₂ E₁ E₂ P Q τ} Hτ y x /.
