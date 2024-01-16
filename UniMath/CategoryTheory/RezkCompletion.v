From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
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

