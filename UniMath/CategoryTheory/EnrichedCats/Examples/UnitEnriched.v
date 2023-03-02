(**********************************************************************

 The unit enriched category

 We construct the unit enriched category and we define some functors
 and natural transformations related to it.

 We write `𝟙` for the unit of the monoidal category. The objects of the
 unit enriched category and inhabitants of the unit type and the
 enrichment is the `𝟙`. As a consequence, the morphisms in this enriched
 category should be isomorphic to `𝟙 --> 𝟙`.

 Note that in this definition we assume that the unit of the involved
 monoidal category `V` is a terminal object, which is usually not
 required in textbooks. The reason for that is that if we don't require
 the unit to be terminal, there could be multiple isomorphisms from `𝟙`
 to `𝟙`. The resulting enriched category is then not guaranteed to be
 univalent.

 Contents
 1. The enrichment of the unit category
 2. Enrichment for functors/natural transformations to the unit

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor.

Section UnitEnrichment.
  Context (V : monoidal_cat)
          (HV : isTerminal V 𝟙).

  (**
   1. The enrichment of the unit category
   *)
  Definition unit_enrichment_data
    : enrichment_data unit_category V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ _ _, 𝟙).
    - exact (λ _, identity _).
    - exact (λ _ _ _, mon_lunitor _).
    - exact (λ _ _ _, identity _).
    - intros x y f.
      apply isapropunit.
  Defined.

  Definition unit_enrichment_laws
    : enrichment_laws unit_enrichment_data.
  Proof.
    repeat split.
    - cbn ; intros x y.
      refine (!_).
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply tensor_id_id.
    - cbn ; intros x y.
      refine (!_).
      refine (_ @ id_left _).
      rewrite mon_lunitor_I_mon_runitor_I.
      apply maponpaths_2.
      apply tensor_id_id.
    - intros w x y z ; cbn.
      apply maponpaths_2.
      etrans.
      {
        rewrite mon_lunitor_I_mon_runitor_I.
        apply idpath.
      }
      apply mon_triangle.
    - cbn ; intros x y f.
      apply isasetunit.
    - cbn ; intros x y f.
      apply (@TerminalArrowEq _ (_ ,, HV)).
    - cbn ; intro x.
      apply isasetunit.
    - cbn ; intros x y z f g.
      apply isasetunit.
  Qed.

  Definition unit_enrichment
    : enrichment unit_category V.
  Proof.
    simple refine (_ ,, _).
    - exact unit_enrichment_data.
    - exact unit_enrichment_laws.
  Defined.

  Definition unit_cat_with_enrichment
    : cat_with_enrichment V
    := pr1 unit_category ,, unit_enrichment.

  (**
   2. Enrichment for functors/natural transformations to the unit
   *)
  Definition functor_to_unit_enrichment
             {C : category}
             (E : enrichment C V)
    : functor_enrichment
        (functor_to_unit C)
        E
        unit_enrichment.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, TerminalArrow (_ ,, HV) _).
    - abstract
        (repeat split ;
         intros ;
         apply (@TerminalArrowEq _ (_ ,, HV))).
  Defined.

  Definition nat_trans_to_unit_enrichment
             {C : category}
             (E : enrichment C V)
             {F G : C ⟶ unit_category}
             (EF : functor_enrichment F E unit_enrichment)
             (EG : functor_enrichment F E unit_enrichment)
    : nat_trans_enrichment
        (unit_category_nat_trans F G)
        EF
        EG.
  Proof.
    intros x y ; cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite mon_lunitor_I_mon_runitor_I.
      apply tensor_runitor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply tensor_lunitor.
    }
    rewrite !assoc.
    apply (@TerminalArrowEq _ (_ ,, HV)).
  Qed.

  Definition constant_functor_enrichment
             (E : cat_with_enrichment V)
             (x : E)
    : functor_enrichment
        (constant_functor unit_cat_with_enrichment E x)
        unit_cat_with_enrichment
        E.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, enriched_id _ _).
    - repeat split.
      + abstract
          (intros y ; cbn ;
           apply id_left).
      + abstract
          (intros y₁ y₂ y₃ ; cbn ;
           rewrite tensor_split ;
           rewrite assoc' ;
           rewrite <- enrichment_id_left ;
           rewrite tensor_lunitor ;
           apply idpath).
      + abstract
          (intros y₁ y₂ f ; cbn ;
           rewrite enriched_from_arr_id ;
           rewrite id_left ;
           apply idpath).
  Defined.

  Definition functor_from_unit_cat_with_enrichment
             (E : cat_with_enrichment V)
             (x : E)
    : functor_with_enrichment unit_cat_with_enrichment E.
  Proof.
    simple refine (_ ,, _).
    - exact (constant_functor unit_cat_with_enrichment E x).
    - exact (constant_functor_enrichment E x).
  Defined.

  Definition constant_nat_trans_enrichment
             {C : category}
             (E : enrichment C V)
             {x y : C}
             (f : x --> y)
    : nat_trans_enrichment
        (constant_nat_trans _ f)
        (constant_functor_enrichment (C ,, E) x)
        (constant_functor_enrichment (C ,, E) y).
  Proof.
    intros z₁ z₂ ; cbn.
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      rewrite mon_lunitor_I_mon_runitor_I.
      etrans.
      {
        apply maponpaths_2.
        apply mon_rinvunitor_runitor.
      }
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      rewrite tensor_runitor.
      rewrite !assoc.
      rewrite mon_runitor_I_mon_lunitor_I.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_lunitor.
      }
      apply id_left.
    }
    apply idpath.
  Qed.
End UnitEnrichment.
