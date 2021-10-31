

(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of heterogeneous substitution systems
-    Various lemmas about the substitution ("bracket") operation
-    Definition of precategory of substitution systems



************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .

Declare Scope subsys.
Delimit Scope subsys with subsys.
Notation "G • F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35) : subsys.
Notation "α ⋆ β" := (horcomp β α) (at level 20) : subsys.

Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25) : subsys.
Notation "Z ∘ α" := (post_whisker α Z) : subsys.

Notation "` T" := (alg_carrier _ T) (at level 3, format "` T") : subsys.
Notation "α •• Z" :=  (# (pre_composition_functor_data _ _ _ Z) α) (at level 25) : subsys.
Notation "A ⊗ B" := (make_catbinprod A B) : subsys.
Notation "A ⊠ B" := (category_binproduct A B) (at level 38) : subsys.
Notation "'ℓ'" := (pre_composition_functor(*_data*) _ _ _) : subsys.
Notation "Z 'p•' Z'" := (ptd_compose _ Z Z') (at level 25) : subsys. (** used to stand for (ptd_composite _ _ Z Z') *)

(** The forgetful functor from pointed endofunctors to endofunctors *)
Notation "'U'" := (functor_ptd_forget _ ) : subsys.
