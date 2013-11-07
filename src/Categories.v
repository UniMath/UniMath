Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "b <-- a" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).
Local Notation "f 'oo'  g" := (precategories.compose f g) (at level 50).

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr).

Ltac prop p := apply (hProppair p); prop_logic.

Module Products.
  Module Finite.

    Definition isInitialObject {C:precategory} (a:C) : hProp.
      prop (forall (x:C), iscontr (a --> x)).
    Defined.

    Definition isTerminalObject {C:precategory} (a:C) : hProp.
      prop (forall (x:C), iscontr (a <-- x)).
    Defined.

    Definition InitialObject (C:precategory) := total2 (fun a:C => isInitialObject a).

    Definition TerminalObject (C:precategory) := total2 (fun a:C => isTerminalObject a).

    Definition hasInitialObject (C:precategory) : hProp.
      prop (ishinh (InitialObject C)).
    Defined.

    Definition hasTerminalObject (C:precategory) : hProp.
      prop (ishinh (TerminalObject C)).
    Defined.

    Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : hProp.
      prop (
          forall p' (f' : p' --> a) (g' : p' --> b),
            iscontr ( total2 ( fun h => dirprod (f o h = f') (g o h = g')))).
    Defined.

    Definition isBinaryCoproduct {C:precategory} {a b p : C} (f : p <-- a) (g : p <-- b) : hProp.
      prop (
          forall p' (f' : p' <-- a) (g' : p' <-- b),
            iscontr ( total2 ( fun h => dirprod (f oo h = f') (g oo h = g')))).
    Defined.

    Definition BinaryProduct {C:precategory} (a b : C) := 
      total2 (fun p => 
      total2 (fun f : p --> a => 
      total2 (fun g : p --> b => 
            isBinaryProduct f g))).

    Definition BinaryCoproduct {C:precategory} (a b : C) := 
      total2 (fun p => 
      total2 (fun f : p <-- a => 
      total2 (fun g : p <-- b => 
            isBinaryCoproduct f g))).

    Definition hasBinaryProducts (C:precategory) : hProp.
      prop (forall a b : C, ishinh (BinaryProduct a b)).
    Defined.

    Definition hasBinaryCoproducts (C:precategory) : hProp.
      prop (forall a b : C, ishinh (BinaryCoproduct a b)).
    Defined.

  End Finite.
End Products.
