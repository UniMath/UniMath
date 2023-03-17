(********************************************************************

 Self-enriched categories

 We show that every symmetric monoidal category can be enriched
 over itself. We also show that every strong monad gives rise to an
 enriched monad.

 Contents
 1. Self-enrichment
 2. Strong monad to enriched monad

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.StrongMonad.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section SelfEnrichment.
  Context (V : sym_mon_closed_cat).

  (**
   1. Self-enrichment
   *)
  Definition self_enrichment_data
    : enrichment_data V V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, x ⊸ y).
    - exact internal_id.
    - exact internal_comp.
    - exact (@internal_from_arr V).
    - exact (@internal_to_arr V).
  Defined.

  Proposition self_enrichment_laws
    : enrichment_laws self_enrichment_data.
  Proof.
    repeat split.
    - exact internal_id_left.
    - exact internal_id_right.
    - exact internal_assoc.
    - exact (@internal_to_from_arr V).
    - exact (@internal_from_to_arr V).
    - exact internal_to_arr_id.
    - exact (@internal_to_arr_comp V).
  Qed.

  Definition self_enrichment
    : enrichment V V.
  Proof.
    simple refine (_ ,, _).
    - exact self_enrichment_data.
    - exact self_enrichment_laws.
  Defined.

  (**
   2. Strong monad to enriched monad
   *)
  Section StrengthToFunctorEnrichment.
    Context {F : V ⟶ V}
            (tF : left_strength F).

    Proposition strength_to_enrichment_laws
      : @is_functor_enrichment
          _ _ _
          F
          self_enrichment self_enrichment
          (λ x y, internal_lam (tF (internal_hom x y) x · # F (internal_eval x y))).
    Proof.
      repeat split.
      - intros x ; cbn.
        use internal_funext.
        intros w h.
        refine (!_).
        etrans.
        {
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_id.
          rewrite internal_beta.
          rewrite tensor_lunitor.
          apply idpath.
        }
        refine (!_).
        rewrite tensor_split.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- functor_id.
          rewrite (left_strength_natural tF).
          rewrite !assoc'.
          rewrite <- functor_comp.
          unfold internal_id.
          rewrite internal_beta.
          rewrite left_strength_mon_lunitor.
          apply idpath.
        }
        rewrite tensor_lunitor.
        apply idpath.
      - intros x y z ; cbn.
        use internal_funext.
        intros w h.
        etrans.
        {
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        etrans.
        {
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            rewrite tensor_split.
            rewrite <- functor_id.
            rewrite !assoc'.
            rewrite left_strength_natural.
            apply idpath.
          }
          rewrite !assoc'.
          rewrite <- !functor_comp.
          unfold internal_comp.
          rewrite internal_beta.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          unfold internal_comp.
          rewrite internal_beta.
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
        rewrite !tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- tensor_lassociator.
        rewrite tensor_id_id.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !assoc.
            rewrite left_strength_natural.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- left_strength_mon_lassociator.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite <- !functor_comp.
        apply idpath.
      - intros x y f ; cbn.
        use internal_funext.
        intros w h.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        refine (!_).
        etrans.
        {
          rewrite tensor_split.
          rewrite <- functor_id.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite left_strength_natural.
          rewrite !assoc'.
          rewrite <- functor_comp.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite functor_comp.
          rewrite !assoc.
          rewrite left_strength_mon_lunitor.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lunitor.
        refine (!_).
        etrans.
        {
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        apply idpath.
    Qed.

    Definition strength_to_enrichment
      : functor_enrichment F self_enrichment self_enrichment.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y, internal_lam (tF _ _ · #F (internal_eval x y))).
      - exact strength_to_enrichment_laws.
    Defined.
  End StrengthToFunctorEnrichment.

  Section StrengthToMonadEnrichment.
    Context {M : Monad V}
            (tM : left_strong_monad M).

    Proposition monad_left_strong_to_enrichment_eta
      : nat_trans_enrichment
          (η M)
          (functor_id_enrichment self_enrichment)
          (strength_to_enrichment tM).
    Proof.
      intros x y ; cbn.
      use internal_funext.
      intros w h.
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        unfold internal_from_arr.
        rewrite internal_beta.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- mon_triangle.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite mon_rinvunitor_runitor.
        rewrite id_right.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_id_id.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_lunitor_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_linvunitor_lunitor.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      apply maponpaths.
      refine (nat_trans_ax (η M) _ _ (internal_eval x y) @ _).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply (left_strong_monad_unit tM).
    Qed.

    Proposition monad_left_strong_to_enrichment_mu
      : nat_trans_enrichment
          (μ M)
          (functor_comp_enrichment
             (strength_to_enrichment tM)
             (strength_to_enrichment tM))
          (strength_to_enrichment tM).
    Proof.
      intros x y ; cbn.
      use internal_funext.
      intros w h.
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          unfold internal_from_arr.
          rewrite internal_beta.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_comp_id_l.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- mon_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_rinvunitor_runitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply left_strong_monad_mu.
      }
      etrans.
      {
        rewrite !assoc'.
        do 3 apply maponpaths.
        exact (!(nat_trans_ax (μ M) _ _ (internal_eval x y))).
      }
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite tensor_split.
          unfold internal_from_arr.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite tensor_lunitor.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_lunitor_triangle.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite mon_linvunitor_lunitor.
        apply idpath.
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- functor_id.
      rewrite left_strength_natural.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite internal_beta.
      apply idpath.
    Qed.

    Definition monad_left_strong_to_enrichment
      : monad_enrichment self_enrichment M
      := strength_to_enrichment tM
         ,,
         monad_left_strong_to_enrichment_eta
         ,,
         monad_left_strong_to_enrichment_mu.
  End StrengthToMonadEnrichment.
End SelfEnrichment.
