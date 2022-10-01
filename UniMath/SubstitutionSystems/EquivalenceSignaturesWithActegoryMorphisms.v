(** Links signatures to lax morphisms in suitable actegories, by exploiting the already established link with action-based strength (in the non-whiskered setting)

Author: Ralph Matthes 2022

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.Actions.
Require Import UniMath.Bicategories.MonoidalCategories.ConstructionOfActions.
Require Import UniMath.Bicategories.MonoidalCategories.ActionOfEndomorphismsInBicat.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrength.
Require Import UniMath.Bicategories.MonoidalCategories.MonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrongFunctorCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.SubstitutionSystems.ActionBasedStrengthOnHomsInBicat.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsWhiskeredMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.ActionOfEndomorphismsInBicatWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.

Import Bicat.Notations.
Import MonoidalNotations.

Local Open Scope cat.

Section A.

  Context (C D D' : category).

  Local Definition Mon_endo' : monoidal_cat := swapping_of_monoidal_cat (monoidal_cat_of_pointedfunctors C).
  Local Definition domain_action : Actions.action Mon_endo' (hom(C:=bicat_of_cats) C D')
    := ActionBasedStrengthOnHomsInBicat.ab_strength_domain_action(C:=bicat_of_cats) C D' (ActionBasedStrengthOnHomsInBicat.forget C).
 Local Definition target_action : Actions.action Mon_endo' (hom(C:=bicat_of_cats) C D)
    := ActionBasedStrengthOnHomsInBicat.ab_strength_target_action(C:=bicat_of_cats) C D (ActionBasedStrengthOnHomsInBicat.forget C).

 Lemma weqSignatureABStrength : Signature C D D' ≃ actionbased_strong_functor Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') (ActionBasedStrengthOnHomsInBicat.target_action C D).
 Proof.
   use weq_iso.
   - apply ab_strong_functor_from_signature.
   - apply signature_from_strong_functor.
   - apply roundtrip1_ob_as_equality.
   - apply roundtrip2_ob_as_equality.
 Defined.

 (* Local Definition endo : category := [C,C]. would not be okay for convertibility *)
 Local Definition endofrombicat : category := ActionOfEndomorphismsInBicatWhiskered.endocat(C:=bicat_of_cats) C.
 Local Definition Mon_endo : monoidal endofrombicat := ActionOfEndomorphismsInBicatWhiskered.Mon_endo(C:=bicat_of_cats) C.
 Local Definition ptdendo : category := coslice_cat_total (ActionOfEndomorphismsInBicatWhiskered.endocat(C:=bicat_of_cats) C)
                                          I_{Mon_endo}.
 Local Definition Mon_ptdendo : monoidal ptdendo
   := monoidal_pointed_objects Mon_endo.

 Local Definition actegoryPtdEndosOnFunctors (E : category) : actegory Mon_ptdendo [C,E]
   := lifted_actegory Mon_endo (actegoryfromprecomp C E) (monoidal_pointed_objects Mon_endo)
        (forget_monoidal_pointed_objects_monoidal Mon_endo).

 Section AA.

 Context (H : [C, D'] ⟶ [C, D]).

 Lemma weqABStrengthLaxMorphismActegories :
   actionbased_strength Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
                                  (ActionBasedStrengthOnHomsInBicat.target_action C D) H
   ≃ lineator_lax Mon_ptdendo (actegoryPtdEndosOnFunctors D') (actegoryPtdEndosOnFunctors D) H.
 Proof.
   use weq_iso.
 Admitted.

End AA.

 Lemma weqSignatureLaxMorphismActegories :
   Signature C D D' ≃ hom(C:=actbicat Mon_ptdendo) ([C, D'],,actegoryPtdEndosOnFunctors D') ([C, D],,actegoryPtdEndosOnFunctors D).
 Proof.
   apply (weqcomp weqSignatureABStrength).
   apply weqfibtototal.
   intro H.
   apply weqABStrengthLaxMorphismActegories.
 Defined.

End A.
