Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "b <-- a" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).
Local Notation "f ;;  g" := (precategories.compose f g) (at level 50).

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr).

Ltac prop p := apply (hProppair p); prop_logic.

Module Products.
  Module Finite.

    Definition isInitial {C:precategory} (a:C) : hProp.
      prop (forall (x:C), iscontr (a --> x)).
    Defined.

    Definition isTerminal {C:precategory} (a:C) : hProp.
      prop (forall (x:C), iscontr (a <-- x)).
    Defined.

    Definition hasInitial (C:precategory) : hProp.
      prop (ishinh (total2 (fun a:C => isInitial a))).
    Defined.

    Definition hasTerminal (C:precategory) : hProp.
      prop (ishinh (total2 (fun a:C => isTerminal a))).
    Defined.

    Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : hProp.
      prop (
          forall p' (f' : p' --> a) (g' : p' --> b),
            iscontr ( total2 ( fun h => dirprod (f o h = f') (g o h = g')))).
    Defined.

    Definition isBinaryCoproduct {C:precategory} {a b p : C} (f : p <-- a) (g : p <-- b) : hProp.
      prop (
          forall p' (f' : p' <-- a) (g' : p' <-- b),
            iscontr ( total2 ( fun h => dirprod (f ;; h = f') (g ;; h = g')))).
    Defined.

    Definition hasBinaryProducts (C:precategory) : hProp.
      prop (
        forall a b : C, 
          ishinh (
              total2 (fun p => 
              total2 (fun f : p --> a => 
              total2 (fun g : p --> b => 
                        isBinaryProduct f g))))).
    Defined.

    Definition hasBinaryCoproducts (C:precategory) : hProp.
      prop (
        forall a b : C, 
          ishinh (
              total2 (fun p => 
              total2 (fun f : p <-- a => 
              total2 (fun g : p <-- b => 
                        isBinaryCoproduct f g))))).
    Defined.

  End Finite.
End Products.
