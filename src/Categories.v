Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).

Ltac prop_logic := 
  repeat (try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr).

Module Products.
  Module Finite.

    Definition isInitial {C:precategory} (a:C) : hProp.
    Proof.
      apply (hProppair (
        forall (x:C), iscontr (a --> x))).
      prop_logic.
    Defined.

    Definition hasInitial (C:precategory) : hProp.
    Proof.
      apply (hProppair (
        ishinh_UU (
          total2 (fun a:C => isInitial a)))).
      prop_logic.
    Defined.

    Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : hProp.
    Proof.
      apply (hProppair (
        forall p' (f' : p' --> a) (g' : p' --> b),
          iscontr ( total2 ( fun h => dirprod (f o h = f') (g o h = g'))))).
      prop_logic.
    Defined.

    Definition hasBinaryProducts (C:precategory) : hProp.
    Proof.
      apply (hProppair (
        forall a b : C, 
          ishinh_UU (
              total2 (fun p => 
              total2 (fun f : p --> a => 
              total2 (fun g : p --> b => 
                        isBinaryProduct f g)))))).
      prop_logic.
    Defined.

  End Finite.
End Products.
