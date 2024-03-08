(**********************************************************************

 Models of the enriched effect calculus

 In this file, we define models for the enriched effect calculus and
 we follow the following paper:

   http://www.itu.dk/people/mogel/papers/eec.pdf

 In this paper, the authors first define the effect calculus, which is
 closely related to call-by-push-value, and then they extend it with
 linear type formers to obtain the enriched effect calculus.

 The syntax of the enriched effect calculus has similarities to
 call-by-push-value and the computational λ-calculus. There are the
 following judgments:
 - `⊢ Γ Con`, which says that `Γ` is a valid context
 - `⊢ A Ty`, which says that `A` is a value type
 - `⊢ A CTy`, which says that `A` is a computation type
 - `Γ | _ ⊢ t : A`, which says that `t` is a term of type `A`. Note
   that in this judgment, `A` is a value type.
 - `Γ | A ⊢ t : B`, which says that `t` is a term of type `B` given a
   computation of type `A`. Here both `A` and `B` are computation
   types.
 Note that there is a distinction between value types and computation
 types. Terms of value types represent values, while terms of
 computation types represent possibly effectful computations.

 Contents
 1. Definition of models of the enriched calculus
 1.1. Model of the enriched effect calculus
 1.2. Model of the enriched effect calculus with additives

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentAdjunction.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.

Local Open Scope cat.

(**
 1. Definition of models of the enriched calculus
 *)

(**
 1.1. Model of the enriched effect calculus
 *)
Definition eec_model
  : UU
  := ∑ (VC : category)
       (TV : Terminal VC)
       (VP : BinProducts VC)
       (expV : Exponentials VP)
       (V : sym_mon_closed_cat := sym_mon_closed_cartesian_cat VC VP TV expV)
       (C : category)
       (EC : enrichment C V),
     (enriched_adjunction (self_enrichment V) EC)
     ×
     (terminal_enriched EC)
     ×
     (initial_enriched EC)
     ×
     (enrichment_power EC)
     ×
     (enrichment_copower EC)
     ×
     (enrichment_binary_prod EC)
     ×
     (enrichment_binary_coprod EC).

(**
 1.2. Model of the enriched effect calculus with additives
 *)
Definition eec_plus_model
  : UU
  := ∑ (M : eec_model),
     Initial (pr1 M)
     ×
     BinCoproducts (pr1 M).

#[reversible=no] Coercion eec_plus_model_to_eec_model
         (E : eec_plus_model)
  : eec_model
  := pr1 E.
