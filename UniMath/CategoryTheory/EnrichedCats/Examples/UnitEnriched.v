(**********************************************************************

 The unit enriched category

 We construct the unit enriched category and we define some functors
 and natural transformations related to it.

 We give two constructions of this enriched category. For the first
 construction, we assume that the monoidal category is semi-cartesian.
 Writing `𝟙` for the unit of the monoidal category, we define the objects
 and morphisms  of the unit enriched category to be inhabitants of the
 unit type, and the enrichment is given by `𝟙`. As a consequence, the
 morphisms in this enriched category are be isomorphic to `𝟙 --> 𝟙`.

 Note that in this construction we assume that the unit of the involved
 monoidal category `V` is a terminal object, which is usually not
 required in textbooks. The reason for that is that if we don't require
 the unit to be terminal, there could be multiple isomorphisms from `𝟙`
 to `𝟙`. The resulting enriched category is then not guaranteed to be
 univalent.

 For the other construction, we assume that `V` has a terminal object.
 The construction proceeds mostly the same, but the only difference is
 that the enrichment is given by the terminal object. This construction
 always gives rise to a terminal object in the bicategory of enriched
 categories.

 Contents
 1. The enrichment of the unit category
 2. Enrichment for functors/natural transformations to the unit
 3. The enrichment of the unit category via terminal objects
 4. Enrichment for functors/natural transformations to the unit via terminal objects

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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.limits.terminal.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section UnitEnrichment.
  Context (V : monoidal_cat)
          (HV : is_semicartesian V).

  (**
   1. The enrichment of the unit category
   *)
  Definition unit_enrichment_data
    : enrichment_data unit_category V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ _ _, I_{V}).
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
      apply (@TerminalArrowEq _ (_ ,, (HV : isTerminal _ _))).
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

  Proposition precomp_arr_unit_enrichment
              {x y : unit_category}
              (w : unit_category)
              (f : x --> y)
    : precomp_arr
        unit_enrichment
        w
        f
      =
      identity _.
  Proof.
    unfold precomp_arr ; cbn.
    rewrite tensor_id_id.
    rewrite id_right.
    rewrite mon_lunitor_I_mon_runitor_I.
    apply mon_rinvunitor_runitor.
  Qed.

  Proposition postcomp_arr_unit_enrichment
              {x y : unit_category}
              (w : unit_category)
              (f : x --> y)
    : postcomp_arr
        unit_enrichment
        w
        f
      =
      identity _.
  Proof.
    unfold postcomp_arr ; cbn.
    rewrite tensor_id_id.
    rewrite id_right.
    apply mon_linvunitor_lunitor.
  Qed.

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
    - exact (λ x y, TerminalArrow (_ ,, (HV : isTerminal _ _)) _).
    - abstract
        (repeat split ;
         intros ;
         apply (@TerminalArrowEq _ (_ ,, (HV : isTerminal _ _)))).
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
    use nat_trans_enrichment_via_comp.
    intros x y.
    etrans.
    {
      apply maponpaths.
      apply precomp_arr_unit_enrichment.
    }
    refine (id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply postcomp_arr_unit_enrichment.
    }
    refine (id_right _ @ _).
    apply (@TerminalArrowEq _ (_ ,, (HV : isTerminal _ _))).
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
    use nat_trans_enrichment_via_comp.
    intros z₁ z₂ ; cbn.
    rewrite enriched_id_precomp_arr.
    rewrite enriched_id_postcomp_arr.
    apply idpath.
  Qed.
End UnitEnrichment.

Section UnitEnrichmentViaTerminal.
  Context (V : monoidal_cat)
          (T : Terminal V).

  (**
   3. The enrichment of the unit category via terminal objects
   *)
  Definition unit_enrichment_data_from_terminal
    : enrichment_data unit_category V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ _ _, T).
    - exact (λ _, TerminalArrow T _).
    - exact (λ _ _ _, TerminalArrow T _).
    - exact (λ _ _ _, TerminalArrow T _).
    - abstract
        (intros x y f ;
         cbn ;
         apply isapropunit).
  Defined.

  Definition unit_enrichment_laws_from_terminal
    : enrichment_laws unit_enrichment_data_from_terminal.
  Proof.
    repeat split.
    - cbn ; intros x y.
      apply TerminalArrowEq.
    - cbn ; intros x y.
      apply TerminalArrowEq.
    - cbn ; intros w x y z.
      apply TerminalArrowEq.
    - cbn ; intros x y f.
      apply isasetunit.
    - cbn ; intros x y f.
      apply (@TerminalArrowEq _ T).
    - cbn ; intro x.
      apply isasetunit.
    - cbn ; intros x y z f g.
      apply isasetunit.
  Qed.

  Definition unit_enrichment_from_terminal
    : enrichment unit_category V.
  Proof.
    simple refine (_ ,, _).
    - exact unit_enrichment_data_from_terminal.
    - exact unit_enrichment_laws_from_terminal.
  Defined.

  Definition unit_cat_with_enrichment_from_terminal
    : cat_with_enrichment V
    := pr1 unit_category ,, unit_enrichment_from_terminal.

  (**
   4. Enrichment for functors/natural transformations to the unit via terminal objects
   *)
  Definition functor_to_unit_enrichment_from_terminal
             {C : category}
             (E : enrichment C V)
    : functor_enrichment
        (functor_to_unit C)
        E
        unit_enrichment_from_terminal.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, TerminalArrow T _).
    - abstract
        (repeat split ;
         intros ;
         apply (@TerminalArrowEq _ T)).
  Defined.

  Definition nat_trans_to_unit_enrichment_from_terminal
             {C : category}
             (E : enrichment C V)
             {F G : C ⟶ unit_category}
             (EF : functor_enrichment F E unit_enrichment_from_terminal)
             (EG : functor_enrichment F E unit_enrichment_from_terminal)
    : nat_trans_enrichment
        (unit_category_nat_trans F G)
        EF
        EG.
  Proof.
    intros x y ; cbn.
    rewrite !assoc'.
    apply TerminalArrowEq.
  Qed.
End UnitEnrichmentViaTerminal.
