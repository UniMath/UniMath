Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Module Products.
  Module Finite.
    Definition isInitial (C:precategory) (a:ob C) : Type := forall (x:ob C), iscontr (a --> x).
    Lemma isaprop_isInitial (C:precategory) (a:ob C) : isaprop (isInitial C a).
      unfold isInitial, isaprop.
      apply impred.
      intro x.
      apply isapropiscontr.
    Defined.

    Definition hasInitial (C:precategory) := total2 (isInitial C).
  End Finite.
End Products.
