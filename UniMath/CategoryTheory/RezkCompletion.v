Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.WeakEquivalences.

Local Open Scope cat.

Section DefinitionRezkCompletion.

  Definition rezk_completion_type
    (A : category)
    : UU
    := ∑ (D : univalent_category), weak_equiv A D.

  Definition RezkCat : UU
    := ∏ C : category, rezk_completion_type C.

End DefinitionRezkCompletion.

