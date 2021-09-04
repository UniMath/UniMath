(** * ω-cocontinuous functors organized as category

This file contains theory about the category of omega-cocontinuous functors, i.e. functors
which preserve sequential colimits ([is_omega_cocont]).

Author: Ralph Matthes 2021
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.

Local Open Scope cat.

Section cat_def.

  Context (C D : precategory).
  Context (hs : has_homsets D).

  Definition omegacocont_precat: sub_precategories [C, D, hs].
  Proof.
    use full_sub_precategory.
    intro F.
    use tpair.
    - exact (is_omega_cocont F).
    - apply isaprop_is_omega_cocont.
  Defined.

  Definition forget_omegacocont: functor omegacocont_precat [C, D, hs].
  Proof.
    apply sub_precategory_inclusion.
  Defined.

  Definition fully_faithful_forget_omegacocont: fully_faithful forget_omegacocont.
  Proof.
    apply fully_faithful_sub_precategory_inclusion.
  Defined.

  Lemma forget_omegacocont_reflects_all_colimits: reflects_all_colimits forget_omegacocont.
  Proof.
    apply fully_faithful_reflects_all_colimits, fully_faithful_forget_omegacocont.
  Qed.


End cat_def.
