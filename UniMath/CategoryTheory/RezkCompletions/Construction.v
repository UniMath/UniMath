(**************************************************************************************************

  The Rezk completion

  For any category A, there exists a univalent category D with a weak equivalence F : A ⟶ D.
  D consists of all objects in PreShv H that are isomorphic to the Yoneda embedding of an object in
  A. This is called the Rezk completion of A.
  Since F is a weak equivalence, precomposition with it gives an adjoint equivalence between the
  functor categories [A, C] and [D, C], and also between [A^op, C] and [D^op, C], for any univalent
  category C.

  Contents
  1. The construction of the Rezk completion and the embedding F [Rezk_completion] [Rezk_eta]
  2. The equivalences between the functor categories
    [Rezk_eta_adj_equiv] [Rezk_eta_Universal_Property]
    [Rezk_op_adj_equiv] [Rezk_op_Universal_Property]

  Original authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman
    january 2013

 **************************************************************************************************)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.

Require Export UniMath.CategoryTheory.RezkCompletions.RezkCompletions.

Local Open Scope cat.

(** * 2. The construction of the Rezk completion and the embedding F *)

Section RezkCompletion.

  Context (A : category).

  Definition Rezk_completion_category : category.
  Proof.
    exists (full_img_sub_precategory (yoneda A)).
    exact (has_homsets_full_img_sub_precategory (yoneda A)).
  Defined.

  Definition Rezk_completion_univalent_category : univalent_category.
  Proof.
    exists Rezk_completion_category.
    apply is_univalent_full_sub_category.
    apply (is_univalent_functor_category _ _ is_univalent_HSET).
  Defined.

  Definition Rezk_eta : functor A Rezk_completion_univalent_category.
  Proof.
    apply (functor_full_img (yoneda A)).
  Defined.

  Lemma Rezk_eta_fully_faithful : fully_faithful Rezk_eta.
  Proof.
    apply (functor_full_img_fully_faithful_if_fun_is _ _ (yoneda A)).
    apply yoneda_fully_faithful.
  Defined.

  Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
  Proof.
    apply (functor_full_img_essentially_surjective _ _ (yoneda A)).
  Defined.

  Definition Rezk_completion
    : rezk_completion A.
  Proof.
    use make_rezk_completion.
    - exact Rezk_completion_univalent_category.
    - exact Rezk_eta.
    - exact Rezk_eta_essentially_surjective.
    - exact Rezk_eta_fully_faithful.
  Defined.

  Section UniversalProperty.

    Context (C : category).
    Context (Ccat : is_univalent C).

    Definition Rezk_eta_adj_equiv
      : adj_equivalence_of_cats (pre_composition_functor A Rezk_completion C Rezk_eta)
      := rezk_completion_functor_equivalence _ Rezk_completion _ Ccat.

    Definition Rezk_eta_Universal_Property
      : isweq (pre_composition_functor _ _ C Rezk_eta)
      := rezk_completion_universal_property _ Rezk_completion _ Ccat.

    Definition Rezk_eta_weq
      : [Rezk_completion, C] ≃ [A, C]
      := make_weq _ Rezk_eta_Universal_Property.

    Definition Rezk_op_adj_equiv
      : adj_equivalence_of_cats
        (pre_composition_functor A^op Rezk_completion^op C
            (functor_opp Rezk_eta))
      := rezk_completion_opp_functor_equivalence A Rezk_completion _ Ccat.

    Definition Rezk_op_Universal_Property
      : isweq (pre_composition_functor A^op Rezk_completion^op C (functor_opp Rezk_eta))
      := rezk_completion_opp_universal_property _ Rezk_completion _ Ccat.

    Definition Rezk_opp_weq
      : [Rezk_completion^op, C] ≃ [A^op, C]
      := make_weq _ Rezk_op_Universal_Property.

  End UniversalProperty.

End RezkCompletion.
