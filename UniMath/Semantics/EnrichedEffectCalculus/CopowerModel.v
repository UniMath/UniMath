(**********************************************************************

 The copower model

 In this file, we formalize Proposition 6.9 from the following paper:

   http://www.itu.dk/people/mogel/papers/eec.pdf

 Contents:
 1. Copower adjunction
 1.1. The functors
 1.2. The unit and counit
 1.3. The adjunction
 2. The copower model

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentAdjunction.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.Examples.SelfEnrichedLimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.Examples.OppositeEnrichedLimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.CopowerFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.Examples.SelfEnrichedColimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.Examples.OppositeEnrichedColimits.
Require Import UniMath.Semantics.EnrichedEffectCalculus.EECModel.

Import MonoidalNotations.
Local Open Scope moncat.
Local Open Scope cat.

Section CopowerModel.
  Context (VC : category)
          (TV : Terminal VC)
          (VP : BinProducts VC)
          (IV : Initial VC)
          (VCP : BinCoproducts VC)
          (expV : Exponentials VP)
          (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
          (C : category)
          (r : C)
          (EC : enrichment C V)
          (TC : terminal_enriched EC)
          (IC : initial_enriched EC)
          (powC : enrichment_power EC)
          (copowC : enrichment_copower EC)
          (PC : enrichment_binary_prod EC)
          (CPC : enrichment_binary_coprod EC).

  Opaque V.

  (**
   1. Copower adjunction
   *)

  (**
   1.1. The functors
   *)
  Definition copow_functor_data
    : functor_data VC C.
  Proof.
    use make_functor_data.
    - exact (λ v, copow_ob copowC v r).
    - exact (λ v₁ v₂ (f : V ⟦ v₁ , v₂ ⟧), copow_mor copowC f r).
  Defined.

  Proposition copow_functor_laws
    : is_functor copow_functor_data.
  Proof.
    split.
    - intro v.
      exact (copow_id_mor copowC v r).
    - intros v₁ v₂ v₃ f g ; cbn.
      exact (copow_comp_mor copowC f g r).
  Qed.

  Definition copow_functor
    : VC ⟶ C.
  Proof.
    use make_functor.
    - exact copow_functor_data.
    - exact copow_functor_laws.
  Defined.

  Proposition copow_functor_enrichment_laws
    : @is_functor_enrichment
        V VC C
        copow_functor (self_enrichment V) EC
        (λ x y, copow_enriched_mor copowC x y r).
  Proof.
    repeat split.
    - intro x.
      use mor_to_copower_eq.
      {
        exact (pr2 (copowC _ r)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply mor_to_copower_commutes.
      }
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_postcomp, is_copower_enriched_map.
      rewrite !internal_beta.
      rewrite tensor_split.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      rewrite !assoc.
      unfold internal_id.
      rewrite internal_beta.
      refine (!_).
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      apply idpath.
    - intros x y z ; cbn.
      use mor_to_copower_eq.
      {
        exact (pr2 (copowC _ r)).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply mor_to_copower_commutes.
      }
      use internal_funext.
      intros a h.
      etrans.
      {
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_postcomp.
        rewrite internal_beta.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        unfold internal_comp.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite <- (copow_enriched_mor_commute copowC y z r).
      etrans.
      {
        rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold is_copower_enriched_map.
        rewrite internal_beta.
        apply idpath.
      }
      refine (!_).
      rewrite !tensor_comp_r_id_r.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        unfold is_copower_enriched_map.
        rewrite internal_beta.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          apply maponpaths.
          rewrite enrichment_assoc.
          apply idpath.
        }
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite !id_left, !id_right.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_split'.
      refine (!_).
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      apply maponpaths.
      clear z a h.
      etrans.
      {
        refine (!_).
        exact (copow_enriched_mor_commute copowC x y r).
      }
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map.
      rewrite internal_beta.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_split'.
      apply idpath.
    - intros x y f ; cbn.
      use mor_to_copower_eq.
      {
        exact (pr2 (copowC _ r)).
      }
      etrans.
      {
        apply copow_mor_commute.
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply mor_to_copower_commutes.
      }
      refine (!_).
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_postcomp.
      rewrite !internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      unfold internal_from_arr.
      rewrite internal_beta.
      apply idpath.
  Qed.

  Definition copow_functor_enrichment
    : functor_enrichment
        copow_functor
        (self_enrichment V)
        EC
    := (λ x y, copow_enriched_mor _ _ _ _)
       ,,
       copow_functor_enrichment_laws.

  Definition hom_l_functor_data
    : functor_data C VC.
  Proof.
    use make_functor_data.
    - exact (λ c, EC ⦃ r , c ⦄).
    - exact (λ c₁ c₂ f, postcomp_arr EC r f).
  Defined.

  Proposition hom_l_functor_laws
    : is_functor hom_l_functor_data.
  Proof.
    split.
    - intro c ; cbn.
      apply (postcomp_arr_id EC).
    - intros c₁ c₂ c₃ f g ; cbn.
      apply (postcomp_arr_comp EC).
  Qed.

  Definition hom_l_functor
    : C ⟶ VC.
  Proof.
    use make_functor.
    - exact hom_l_functor_data.
    - exact hom_l_functor_laws.
  Defined.

  Proposition hom_l_functor_enrichment_laws
    : @is_functor_enrichment
        V C VC
        hom_l_functor EC
        (self_enrichment V)
        (λ x y, internal_lam (enriched_comp EC r x y)).
  Proof.
    repeat split.
    - intro x ; cbn.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      unfold internal_id.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite enrichment_id_left.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    - intros x y z ; cbn.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite !internal_beta.
      refine (!_).
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_comp_l_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_lassociator.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite tensor_id_id.
      apply maponpaths.
      rewrite enrichment_assoc.
      rewrite !assoc.
      apply idpath.
    - intros x y f ; cbn.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_from_arr.
      rewrite !internal_beta.
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

  Definition hom_l_functor_enrichment
    : functor_enrichment
        hom_l_functor
        EC
        (self_enrichment V).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, internal_lam (enriched_comp EC _ _ _)).
    - exact hom_l_functor_enrichment_laws.
  Defined.

  (**
   1.2. The unit and counit
   *)
  Definition copow_adjunction_unit_data
    : nat_trans_data
        (functor_identity VC)
        (copow_functor ∙ hom_l_functor)
    := λ v, mor_of_copow_ob copowC v r.

  Proposition copow_adjunction_unit_enrichment
    : nat_trans_enrichment
        copow_adjunction_unit_data
        (functor_id_enrichment (self_enrichment V))
        (functor_comp_enrichment
           copow_functor_enrichment
           hom_l_functor_enrichment).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite id_left.
    rewrite (self_enrichment_precomp V), (self_enrichment_postcomp V).
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite !internal_beta.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    clear a h.
    rewrite !assoc.
    rewrite <- tensor_split'.
    refine (_ @ copow_enriched_mor_commute copowC _ _ _).
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold is_copower_enriched_map.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.

  Proposition copow_adjunction_unit_laws
    : is_nat_trans
        (functor_identity VC)
        (copow_functor ∙ hom_l_functor)
        (λ v, mor_of_copow_ob copowC v r).
  Proof.
    exact (is_nat_trans_from_enrichment
             copow_adjunction_unit_enrichment).
  Qed.

  Definition copow_adjunction_unit
    : functor_identity VC
      ⟹
      copow_functor ∙ hom_l_functor.
  Proof.
    use make_nat_trans.
    - exact (λ v, mor_of_copow_ob copowC v r).
    - exact copow_adjunction_unit_laws.
  Defined.

  Definition copow_adjunction_counit_data
    : nat_trans_data
        (hom_l_functor ∙ copow_functor)
        (functor_identity C)
    := λ x, copow_on_enriched_mor copowC r x.

  Proposition copow_adjunction_counit_enrichment
    : nat_trans_enrichment
        copow_adjunction_counit_data
        (functor_comp_enrichment
           hom_l_functor_enrichment
           copow_functor_enrichment)
        (functor_id_enrichment EC).
  Proof.
    use nat_trans_enrichment_via_comp.
    unfold copow_adjunction_counit_data.
    intros x y ; cbn.
    rewrite id_left.
    use mor_to_copower_eq.
    {
      exact (pr2 (copowC _ r)).
    }
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply precomp_copow_on_enriched_mor_commute.
    }
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ internal_beta _).
    rewrite !tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    refine (!_).
    rewrite <- mon_linvunitor_lunitor.
    rewrite <- (copow_on_enriched_mor_commute copowC).
    rewrite !tensor_comp_id_r.
    rewrite !assoc'.
    unfold is_copower_enriched_map.
    rewrite !internal_beta.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enriched_comp_postcomp_arr.
      apply idpath.
    }
    unfold postcomp_arr.
    rewrite !assoc.
    rewrite !tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_r_id_r.
    rewrite !id_left.
    etrans.
    {
      rewrite tensor_split'.
      rewrite !assoc'.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite tensor_split'.
      rewrite !assoc'.
      apply idpath.
    }
    apply maponpaths.
    rewrite !assoc.
    rewrite <- !tensor_comp_id_l.
    apply maponpaths.
    refine (!(copow_enriched_mor_commute _ _ _ _) @ _).
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    apply maponpaths.
    unfold is_copower_enriched_map.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition copow_adjunction_counit_laws
    : is_nat_trans
        (hom_l_functor ∙ copow_functor)
        (functor_identity C)
        (λ x, copow_on_enriched_mor copowC r x).
  Proof.
    exact (is_nat_trans_from_enrichment
             copow_adjunction_counit_enrichment).
  Qed.

  Definition copow_adjunction_counit
    : hom_l_functor ∙ copow_functor ⟹ functor_identity C.
  Proof.
    use make_nat_trans.
    - exact (λ x, copow_on_enriched_mor copowC r x).
    - exact copow_adjunction_counit_laws.
  Defined.

  (**
   1.3. The adjunction
   *)
  Definition copow_adjunction_data
    : adjunction_data VC C.
  Proof.
    use make_adjunction_data.
    - exact copow_functor.
    - exact hom_l_functor.
    - exact copow_adjunction_unit.
    - exact copow_adjunction_counit.
  Defined.

  Proposition copow_adjunction_laws
    : form_adjunction' copow_adjunction_data.
  Proof.
    split.
    - intro v ; cbn.
      use arr_to_copower_eq.
      {
        exact (pr2 (copowC _ r)).
      }
      rewrite enriched_from_arr_id.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply arr_to_copower_precomp.
      }
      etrans.
      {
        apply arr_to_copower_commutes.
      }
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map, internal_postcomp.
      rewrite !internal_beta.
      rewrite tensor_split.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear a h.
      refine (!_).
      rewrite !assoc.
      rewrite internal_beta.
      rewrite <- tensor_split'.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      apply maponpaths.
      refine (!(id_right _) @ _).
      apply maponpaths.
      refine (!_).
      unfold postcomp_arr.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      refine (_ @ mon_linvunitor_lunitor _).
      rewrite !assoc'.
      apply maponpaths.
      refine (_ @ copow_on_enriched_mor_commute copowC _ _).
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map.
      rewrite internal_beta.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_split.
      rewrite <- tensor_split'.
      apply idpath.
    - intro x ; cbn.
      unfold postcomp_arr.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      refine (_ @ mon_linvunitor_lunitor _).
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      refine (_ @ copow_on_enriched_mor_commute copowC r x).
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_split'.
      apply idpath.
  Qed.

  Definition copow_adjunction
    : adjunction VC C.
  Proof.
    use make_adjunction.
    - exact copow_adjunction_data.
    - exact copow_adjunction_laws.
  Defined.

  Definition copow_adjunction_enrichment
    : adjunction_enrichment
        copow_adjunction
        (self_enrichment (sym_mon_closed_cartesian_cat VC VP TV expV))
        EC.
  Proof.
    use make_adjunction_enrichment ; cbn.
    - exact copow_functor_enrichment.
    - exact hom_l_functor_enrichment.
    - exact copow_adjunction_unit_enrichment.
    - exact copow_adjunction_counit_enrichment.
  Defined.

  Definition copow_enriched_adjunction
    : enriched_adjunction
        (self_enrichment (sym_mon_closed_cartesian_cat VC VP TV expV))
        EC
    := copow_adjunction ,, copow_adjunction_enrichment.

  (**
   2. The copower model
   *)
  Definition copow_eec_model
    : eec_model
    := VC
       ,,
       TV
       ,,
       VP
       ,,
       expV
       ,,
       C
       ,,
       EC
       ,,
       copow_enriched_adjunction
       ,,
       TC
       ,,
       IC
       ,,
       powC
       ,,
       copowC
       ,,
       PC
       ,,
       CPC.

  Definition copow_eec_plus_model
    : eec_plus_model
    := copow_eec_model ,, IV ,, VCP.
End CopowerModel.
