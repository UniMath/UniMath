Require Import RezkCompletion.precategories.
Require Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropishinh);
  try (apply isapropiscontr).

Module Products.
  Module Finite.

    Definition isInitial {C:precategory} (a:C) : hProp.
    Proof.
      set (prop := forall (x:C), iscontr (a --> x)).
      apply (hProppair prop).
      prop_logic.
    Defined.

    Definition hasInitial (C:precategory) : hProp.
    Proof.
      set (prop := ishinh (total2 (fun a:C => isInitial a))).
      apply (hProppair prop).
      prop_logic.
    Defined.

    Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : hProp.
    Proof.
      set (prop := forall p' (f' : p' --> a) (g' : p' --> b),
          iscontr ( total2 ( fun h => dirprod (f o h = f') (g o h = g')))).
      apply (hProppair prop).
      prop_logic.
    Defined.

    Definition hasBinaryProducts (C:precategory) : hProp.
    Proof.
      apply (hProppair (
        forall a b : C, 
          ishinh (
              total2 (fun p => 
              total2 (fun f : p --> a => 
              total2 (fun g : p --> b => 
                        isBinaryProduct f g)))))).
      prop_logic.
    Defined.

  End Finite.
End Products.
