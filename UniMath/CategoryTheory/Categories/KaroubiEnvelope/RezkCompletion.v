(**************************************************************************************************

  The Rezk Completion of the Setcategory Karoubi Envelope

  This file shows that the univalent Karoubi envelope construction is the Rezk completion of the
  setcategory Karoubi envelope. The proof proceeds via the "alternative (but equivalent) definition"
  of the setcategory Karoubi envelope, which is constructed similarly to the univalent Karoubi
  envelope, minus a propositional truncation.

  Contents
  1. The packaging of the Rezk completion [karoubi_Rezk_completion]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.Core.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.SetKaroubi.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.UnivalentKaroubi.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.RezkCompletions.RezkCompletions.

Local Open Scope cat.

(** * 1. The packaging of the Rezk completion *)

Section RezkCompletion.

  Context (C : category).

  Definition karoubi_rezk_completion_cat
    : univalent_category
    := make_univalent_category
      (univalent_karoubi C)
      (univalent_karoubi_envelope_is_univalent _).

  Definition karoubi_rezk_completion_inclusion
    : set_karoubi_cat C ⟶ karoubi_rezk_completion_cat
    := set_karoubi_equivalence_functor _ ∙ truncation_functor _.

  Definition karoubi_rezk_completion_essentially_surjective
    : essentially_surjective karoubi_rezk_completion_inclusion
    := comp_essentially_surjective _
      (λ X, hinhpr (set_karoubi_equivalence_split_essentially_surjective C X)) _
      (truncation_functor_essentially_surjective _).

  Definition karoubi_rezk_completion_fully_faithful
    : fully_faithful karoubi_rezk_completion_inclusion
    := comp_ff_is_ff _ _ _ _
      (set_karoubi_equivalence_fully_faithful C) _
      (truncation_functor_fully_faithful _).

  Definition karoubi_rezk_completion
    : rezk_completion (set_karoubi_cat C)
    := make_rezk_completion
      karoubi_rezk_completion_cat
      karoubi_rezk_completion_inclusion
      karoubi_rezk_completion_essentially_surjective
      karoubi_rezk_completion_fully_faithful.

End RezkCompletion.
