(*************************************************************************

 Lemmas for fully faithful enriched functors

 This file collects several lemmas on fully faithful enriched functors.
 The current lemmas are:
 - If `G` and `F ∙ G` are fully faithful, then `F` is fully faithful
   as well ([fully_faithful_enriched_precomp])
 - Fully faithful functors are closed under natural isomorphis
   ([fully_faithful_enriched_nat_z_iso])
 We also use these lemmas for a factorization lemma for fully faithful
 functors ([fully_faithful_enriched_factorization_precomp]).

 Contents
 1. Composition of fully faithful functors
 2. Fully faithful functors are closed under natural isomorphism
 3. Factorization of fully faithful functors

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.

(** * 1. Composition of fully faithful functors *)
Section FullyFaithfulPrecomp.
  Context {C₁ C₂ C₃ : category}
          {F : C₁ ⟶ C₂}
          {G : C₂ ⟶ C₃}
          {V : monoidal_cat}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (EF : functor_enrichment F E₁ E₂)
          (EG : functor_enrichment G E₂ E₃)
          (HFG : fully_faithful_enriched_functor (functor_comp_enrichment EF EG))
          (HG : fully_faithful_enriched_functor EG).

  Section Iso.
    Context (x y  : C₁).

    Let φ : z_iso (E₁ ⦃ x , y ⦄) (E₃ ⦃ G (F x) , G (F y) ⦄)
      := fully_faithful_enriched_functor_z_iso HFG x y.
    Let ψ : z_iso _ _
      := fully_faithful_enriched_functor_z_iso HG (F x) (F y).

    Definition fully_faithful_precomp_inv
      : E₂ ⦃ F x , F y ⦄ --> E₁ ⦃ x , y ⦄
      := EG (F x) (F y) · inv_from_z_iso φ.

    Proposition fully_faithful_precomp_inv_right
      : EF x y · fully_faithful_precomp_inv = identity _.
    Proof.
      unfold fully_faithful_precomp_inv.
      rewrite !assoc.
      refine (_ @ z_iso_inv_after_z_iso φ).
      apply maponpaths_2.
      apply idpath.
    Qed.

    Proposition fully_faithful_precomp_inv_left
      : fully_faithful_precomp_inv · EF x y = identity _.
    Proof.
      unfold fully_faithful_precomp_inv.
      refine (_ @ z_iso_inv_after_z_iso ψ).
      rewrite !assoc'.
      apply maponpaths.
      refine (!(id_right _) @ _).
      rewrite <- (z_iso_inv_after_z_iso ψ).
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite !assoc'.
      apply z_iso_after_z_iso_inv.
    Qed.
  End Iso.

  Proposition fully_faithful_enriched_precomp
    : fully_faithful_enriched_functor EF.
  Proof.
    intros x y.
    use make_is_z_isomorphism.
    - exact (fully_faithful_precomp_inv x y).
    - split.
      + exact (fully_faithful_precomp_inv_right x y).
      + exact (fully_faithful_precomp_inv_left x y).
  Qed.
End FullyFaithfulPrecomp.

(** * 2. Fully faithful functors are closed under natural isomorphism *)
Section FullyFaithfulIso.
  Context {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          {α : nat_z_iso F G}
          {V : monoidal_cat}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {EF : functor_enrichment F E₁ E₂}
          {EG : functor_enrichment G E₁ E₂}
          (Hα : nat_trans_enrichment α EF EG)
          (HF : fully_faithful_enriched_functor EF).

  Section Iso.
    Context (x y : C₁).

    Let φ : z_iso (E₁ ⦃ x , y ⦄) (E₂ ⦃ F x , F y ⦄)
      := fully_faithful_enriched_functor_z_iso HF x y.

    Definition fully_faithful_enriched_nat_z_iso_inv
      : E₂ ⦃ G x , G y ⦄ --> E₁ ⦃ x, y ⦄
      := precomp_arr _ _ (α x)
         · postcomp_arr _ _ (inv_from_z_iso (nat_z_iso_pointwise_z_iso α y))
         · inv_from_z_iso φ.

    Arguments fully_faithful_enriched_nat_z_iso_inv /.

    Proposition fully_faithful_enriched_nat_z_iso_inv_right
      : EG x y · fully_faithful_enriched_nat_z_iso_inv = identity _.
    Proof.
      cbn.
      refine (_ @ z_iso_inv_after_z_iso φ).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite (nat_trans_enrichment_to_comp Hα x y).
      rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      etrans.
      {
        do 2 apply maponpaths.
        exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso α y)).
      }
      rewrite postcomp_arr_id.
      apply id_right.
    Qed.

    Proposition fully_faithful_enriched_nat_z_iso_inv_left
      : fully_faithful_enriched_nat_z_iso_inv · EG x y = identity _.
    Proof.
      cbn.
      refine (_ @ postcomp_arr_id _ _ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso α y))).
      }
      cbn.
      rewrite precomp_postcomp_arr.
      rewrite postcomp_arr_comp.
      rewrite !assoc'.
      apply maponpaths.
      refine (!(id_left _) @ _).
      rewrite <- precomp_arr_id.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso α x))).
      }
      rewrite precomp_arr_comp.
      rewrite !assoc'.
      apply maponpaths.
      rewrite precomp_postcomp_arr.
      etrans.
      {
        apply maponpaths_2.
        refine (!(id_left _) @ _).
        rewrite <- (z_iso_after_z_iso_inv φ).
        rewrite !assoc'.
        apply maponpaths.
        exact (!(nat_trans_enrichment_to_comp Hα x y)).
      }
      rewrite !assoc'.
      rewrite <- precomp_arr_comp.
      etrans.
      {
        do 3 apply maponpaths.
        exact (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso α x)).
      }
      rewrite precomp_arr_id.
      rewrite id_right.
      apply idpath.
    Qed.
  End Iso.

  Proposition fully_faithful_enriched_nat_z_iso
    : fully_faithful_enriched_functor EG.
  Proof.
    intros x y.
    use make_is_z_isomorphism.
    - exact (fully_faithful_enriched_nat_z_iso_inv x y).
    - split.
      + exact (fully_faithful_enriched_nat_z_iso_inv_right x y).
      + exact (fully_faithful_enriched_nat_z_iso_inv_left x y).
  Qed.
End FullyFaithfulIso.

(** * 3. Factorization of fully faithful functors *)
Proposition fully_faithful_enriched_factorization_precomp
            {C₁ C₂ C₃ : category}
            {F : C₁ ⟶ C₃}
            {G : C₁ ⟶ C₂}
            {H : C₂ ⟶ C₃}
            {α : nat_z_iso F (G ∙ H)}
            {V : monoidal_cat}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            (EF : functor_enrichment F E₁ E₃)
            (EG : functor_enrichment G E₁ E₂)
            (EH : functor_enrichment H E₂ E₃)
            (Hα : nat_trans_enrichment α EF (functor_comp_enrichment EG EH))
            (HEF : fully_faithful_enriched_functor EF)
            (HEH : fully_faithful_enriched_functor EH)
  : fully_faithful_enriched_functor EG.
Proof.
  exact (fully_faithful_enriched_precomp
           _ _
           (fully_faithful_enriched_nat_z_iso Hα HEF) HEH).
Qed.
