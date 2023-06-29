(***********************************************************************************

 Modification and indexed transformations

 In this file, we relate modifications and indexed transformations. We can
 directly construct maps back and forth due to the similarity of their definitions.

 Contents
 1. Indexed transformations to modifications
 2. Modifications to indexed transformations

 ***********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PseudoFunctorsIntoCat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.PseudoTransformationIntoCat.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

(**
 1. Indexed transformations to modifications
 *)
Definition indexed_nat_trans_to_modification
           {C : category}
           {Φ Ψ : indexed_cat C}
           {τ θ : indexed_functor Φ Ψ}
           (m : indexed_nat_trans τ θ)
  : modification
      (indexed_functor_to_pstrans τ)
      (indexed_functor_to_pstrans θ).
Proof.
  use make_modification.
  - exact (λ x, m x).
  - abstract
      (intros x y f ; cbn in x, y, f ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intro xx ;
       exact (indexed_nat_trans_natural m f xx)).
Defined.

(**
 2. Modifications to indexed transformations
 *)
Definition modification_to_indexed_nat_trans
           {C : category}
           {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
           {τ θ : pstrans F G}
           (m : modification τ θ)
  : indexed_nat_trans
      (pstrans_to_indexed_functor τ)
      (pstrans_to_indexed_functor θ).
Proof.
  use make_indexed_nat_trans.
  - exact (λ x, m x).
  - abstract
      (intros x y f xx ;
       exact (nat_trans_eq_pointwise (modnaturality_of m x y f) xx)).
Defined.
