(*****************************************************************

 Colimits in self enriched categories

 Contents
 1. Copowers

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section SelfEnrichmentColimits.
  Context (V : sym_mon_closed_cat).

  (**
   1. Copowers
   *)
  Section SelfEnrichmentCopower.
    Context (v₁ v₂ : V).

    Definition self_enrichment_copower_cocone
      : copower_cocone (self_enrichment V) v₁ v₂.
    Proof.
      use make_copower_cocone.
      - exact (v₁ ⊗ v₂).
      - exact (internal_pair v₁ v₂).
    Defined.

    Proposition self_enrichment_is_copower_eq_1
                (w : V)
      : is_copower_enriched_map
          (self_enrichment V)
          v₁ v₂
          self_enrichment_copower_cocone
          w
        · internal_uncurry v₁ v₂ w
        =
        identity _.
    Proof.
      cbn.
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_uncurry.
      rewrite internal_beta.
      unfold is_copower_enriched_map.
      rewrite tensor_split.
      rewrite <- tensor_id_id.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite internal_beta ; cbn.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        unfold internal_pair.
        rewrite internal_beta.
        rewrite tensor_id_id.
        apply id_left.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      apply id_right.
    Qed.

    Proposition self_enrichment_is_copower_eq_2
                (w : V)
      : internal_uncurry v₁ v₂ w
        · is_copower_enriched_map
            (self_enrichment V)
            v₁ v₂
            self_enrichment_copower_cocone
            w
        =
        identity _.
    Proof.
      use internal_funext ; cbn.
      intros a₁ h₁.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map ; cbn.
      rewrite internal_beta.
      use internal_funext ; cbn.
      intros a₂ h₂.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        unfold internal_pair.
        rewrite internal_beta.
        rewrite tensor_id_id.
        apply id_left.
      }
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_uncurry.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    Qed.

    Definition self_enrichment_is_copower
      : is_copower_enriched
          (self_enrichment V)
          v₁ v₂
          self_enrichment_copower_cocone.
    Proof.
      use make_is_copower_enriched.
      - exact (λ w, internal_uncurry v₁ v₂ w).
      - exact self_enrichment_is_copower_eq_1.
      - exact self_enrichment_is_copower_eq_2.
    Defined.
  End SelfEnrichmentCopower.

  Definition self_enrichment_copowers
    : enrichment_copower (self_enrichment V)
    := λ v₁ v₂,
       self_enrichment_copower_cocone v₁ v₂
       ,,
       self_enrichment_is_copower v₁ v₂.
End SelfEnrichmentColimits.
