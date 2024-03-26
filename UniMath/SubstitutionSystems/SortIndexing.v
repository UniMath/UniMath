(** collects the disparate definitions that had been spread over the package SubstitutionSystems

author: Ralph Matthes, March 2024
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.

Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

Section SortIndexing.

  Context (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).


(** Define the category of sorts *)
Definition sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
Definition sortToC : category := [sort_cat,C].
Definition make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Definition make_sortToC_mor (ξ ξ' : sortToC) (fam : ∏ s: sort, pr1 ξ s --> pr1 ξ' s) : sortToC⟦ξ,ξ'⟧
  := nat_trans_functor_path_pregroupoid fam.

Definition BCsortToC (BC: BinCoproducts C) : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
Definition BPsortToC (BP: BinProducts C) : BinProducts sortToC := BinProducts_functor_precat _ _ BP.

Definition sortToCC : category := [sortToC, C].

Definition BPsortToCC (BP: BinProducts C) : BinProducts sortToCC := BinProducts_functor_precat _ _ BP.


End SortIndexing.
