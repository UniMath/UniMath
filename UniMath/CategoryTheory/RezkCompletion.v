Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

Section DefinitionRezkCompletion.

  Definition RezkCat : UU
    := ∏ C : category,
        ∑ D : univalent_category,
          ∑ H : functor C D,
            essentially_surjective H × fully_faithful H.

End DefinitionRezkCompletion.

