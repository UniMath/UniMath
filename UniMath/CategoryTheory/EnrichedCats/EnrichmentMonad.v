(**********************************************************************

 Enriched monads

 In this file, we define the basic notions for enriched monads. More
 specifically, we define enrichments of monads and we define enriched
 monads.

 Contents
 1. Enrichments of monads
 2. Enriched monads

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Enrichments of monads
 *)
Definition monad_enrichment
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
           (M : Monad C)
  : UU
  := ∑ (EM : functor_enrichment M E E),
     nat_trans_enrichment (η M) (functor_id_enrichment _) EM
     ×
     nat_trans_enrichment (μ M) (functor_comp_enrichment EM EM) EM.

#[reversible=no] Coercion endo_of_monad_enrichment
         {V : monoidal_cat}
         {C : category}
         {E : enrichment C V}
         {M : Monad C}
         (EM : monad_enrichment E M)
  : functor_enrichment M E E
  := pr1 EM.

Definition unit_of_monad_enrichment
           {V : monoidal_cat}
           {C : category}
           {E : enrichment C V}
           {M : Monad C}
           (EM : monad_enrichment E M)
  : nat_trans_enrichment (η M) (functor_id_enrichment _) EM
  := pr12 EM.

Definition mu_of_monad_enrichment
           {V : monoidal_cat}
           {C : category}
           {E : enrichment C V}
           {M : Monad C}
           (EM : monad_enrichment E M)
  : nat_trans_enrichment (μ M) (functor_comp_enrichment EM EM) EM
  := pr22 EM.

(**
 2. Enriched monads
 *)
Definition enriched_monad
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∑ (M : Monad C), monad_enrichment E M.

#[reversible=no] Coercion enriched_monad_to_monad
         {V : monoidal_cat}
         {C : category}
         {E : enrichment C V}
         (M : enriched_monad E)
  : Monad C
  := pr1 M.

Definition enriched_monad_enrichment
           {V : monoidal_cat}
           {C : category}
           {E : enrichment C V}
           (M : enriched_monad E)
  : monad_enrichment E M
  := pr2 M.
