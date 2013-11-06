Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).

Module Products.
  Module Finite.
    Definition isInitial {C:precategory} (a:ob C) : Type := forall (x:ob C), iscontr (a --> x).

    Lemma isaprop_isInitial {C:precategory} (a:ob C) : isaprop (isInitial a).
    Proof.
      apply impred.
      intro x.
      apply isapropiscontr.
    Defined.

    Definition hasInitial (C:precategory) := total2 (@isInitial C).

    Definition isBinaryProduct {C:precategory} {a b p : ob C} (f : p --> a) (g : p --> b) :=
      forall (p' : ob C) (f' : p' --> a) (g' : p' --> b),
        iscontr ( total2 ( fun h : p' --> p => dirprod (f o h = f') (g o h = g') )).

    Lemma isaprop_isBinaryProduct {C:precategory} {a b p : ob C} (f : p --> a) (g : p --> b) :
      isaprop (isBinaryProduct f g).
    Proof.
      apply impred.
      intro p'.
      apply impred.
      intro f'.
      apply impred.
      intro g'.
      apply isapropiscontr.
    Defined.

    Definition hasBinaryProducts (C:precategory) := 
      forall a b, 
        total2 (fun p : ob C => 
                  total2 (fun f : p --> a => 
                            total2 (fun g : p --> b => isBinaryProduct f g))).

  End Finite.
End Products.
