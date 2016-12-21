

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


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

Notation "# F" := (functor_on_morphisms F)(at level 3).
Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Notation "G • F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Notation "α ∙∙ β" := (horcomp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).

Notation "` T" := (alg_carrier _ T) (at level 3, format "` T").
Notation "α •• Z" :=  (# (pre_composition_functor_data _ _ _ _ _ Z) α) (at level 25).
Notation "A ⊗ B" := (precatbinprodpair A B) (at level 10).
Notation "A 'XX' B" := (precategory_binproduct A B) (at level 2).
Notation "'ℓ'" := (pre_composition_functor(*_data*) _ _ _ _ _ ).
Notation "Z 'p•' Z'" := (ptd_composite _ _ Z Z') (at level 25).
Notation "'U'" := (functor_ptd_forget _ _ ).
