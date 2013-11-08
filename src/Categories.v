(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import RezkCompletion.precategories.
Import RezkCompletion.pathnotations.PathNotations.
Import Foundations.hlevel2.hSet.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "b <-- a" := (precategory_morphisms a b) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).
Local Notation "f 'oo'  g" := (precategories.compose f g) (at level 50).

(* compare to Foundations.uu0.pathscomp0 *)
Definition pathscomp0' {T:UU} {a b c:T} : a == b -> b == c -> a == c.
Proof. intros e1 e2. destruct e2. assumption. Defined.

Ltac path_via x := apply (@pathscomp0 _ _ x).
Ltac path_via' x := apply (@pathscomp0' _ _ x).
Ltac path_from f := apply (@maponpaths _ _ f).

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropdirprod); try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr);
  try assumption.

Global Opaque isapropiscontr isapropishinh.

Definition mere (X:UU) := forall P:UU, isaprop P -> (X -> P) -> P.

Lemma isaprop_mere (X:UU) : isaprop(mere X).
Proof. prop_logic. Qed.

(** ** products *)

Module Products.

  (** *** initial objects *)

  Definition isInitialObject {C:precategory} (a:C) := forall (x:C), iscontr (a --> x).

  Lemma initialObjectIsomorphy {C:precategory} (a b : C) : isInitialObject a -> isInitialObject b -> iso a b.
  Proof.
    intros ia ib. exists (pr1 (ia b)). exists (pr1 (ib a)).
    split. path_via (pr1 (ia a)). apply (pr2 (ia a)).
    apply pathsinv0. apply (pr2 (ia a)). path_via (pr1 (ib b)). apply (pr2 (ib b)).
    apply pathsinv0. apply (pr2 (ib b)).
  Defined.

  Lemma isaprop_isInitialObject {C:precategory} (a:C) : isaprop(isInitialObject a).
  Proof. prop_logic. Qed.

  Definition isInitialObjectProp {C:precategory} (a:C) := 
    hProppair (isInitialObject a) (isaprop_isInitialObject a) : hProp.

  Definition InitialObject (C:precategory) := total2 (fun a:C => isInitialObject a).

  Definition hasInitialObject (C:precategory) := mere (InitialObject C).

  Definition hasInitialObjectProp (C:precategory) := 
    hProppair (hasInitialObject C) (isaprop_mere _).

  (** *** binary products *)

  Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) :=
    forall p' (f' : p' --> a) (g' : p' --> b),
      iscontr ( total2 ( fun h => dirprod (f o h == f') (g o h == g'))).

  Lemma isaprop_isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : isaprop(isBinaryProduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryProductProp {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) :=
    hProppair (isBinaryProduct f g) (isaprop_isBinaryProduct _ _).

  Definition BinaryProduct {C:precategory} (a b : C) := 
    total2 (fun p => 
              total2 (fun f : p --> a => 
                        total2 (fun g : p --> b => 
                                  isBinaryProduct f g))).

  Definition hasBinaryProducts (C:precategory) := forall a b : C, mere (BinaryProduct a b).

  Lemma isaprop_hasBinaryProducts (C:precategory) : isaprop (hasBinaryProducts C).
  Proof. prop_logic. Qed.

  Definition hasBinaryProductsProp (C:precategory) := 
    hProppair (hasBinaryProducts C) (isaprop_hasBinaryProducts _).

End Products.

(** ** coproducts *)

Module Coproducts.

  (** This module is obtained from the module Products by copying and then reversing arrows from --> to <--,
   reversing composition from o to oo, and changing various words. *)

  (** *** terminal objects *)

  Definition isTerminalObject {C:precategory} (a:C) := forall (x:C), iscontr (a <-- x).

  Lemma isaprop_isTerminalObject {C:precategory} (a:C) : isaprop(isTerminalObject a).
  Proof. prop_logic. Qed.

  Definition isTerminalObjectProp {C:precategory} (a:C) := 
    hProppair (isTerminalObject a) (isaprop_isTerminalObject a) : hProp.

  Definition TerminalObject (C:precategory) := total2 (fun a:C => isTerminalObject a).

  Definition hasTerminalObject (C:precategory) := mere (TerminalObject C).

  Definition hasTerminalObjectProp (C:precategory) := 
    hProppair (hasTerminalObject C) (isaprop_mere _).

  (** *** binary coproducts *)

  Definition isBinaryCoproduct {C:precategory} {a b p : C} (f : p <-- a) (g : p <-- b) :=
    forall p' (f' : p' <-- a) (g' : p' <-- b),
      iscontr ( total2 ( fun h => dirprod (f oo h == f') (g oo h == g'))).

  Lemma isaprop_isBinaryCoproduct {C:precategory} {a b p : C} (f : p <-- a) (g : p <-- b) : isaprop(isBinaryCoproduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryCoproductProp {C:precategory} {a b p : C} (f : p <-- a) (g : p <-- b) :=
    hProppair (isBinaryCoproduct f g) (isaprop_isBinaryCoproduct _ _).

  Definition BinaryCoproduct {C:precategory} (a b : C) := 
    total2 (fun p => 
    total2 (fun f : p <-- a => 
    total2 (fun g : p <-- b => 
          isBinaryCoproduct f g))).

  Definition hasBinaryCoproducts (C:precategory) := forall a b : C, mere (BinaryCoproduct a b).

  Lemma isaprop_hasBinaryCoproducts (C:precategory) : isaprop (hasBinaryCoproducts C).
  Proof. prop_logic. Qed.

  Definition hasBinaryCoproductsProp (C:precategory) := 
    hProppair (hasBinaryCoproducts C) (isaprop_hasBinaryCoproducts _).

End Coproducts.

Module DirectSums.

  Import Coproducts Products.

  Definition isBinarySum {C:precategory} {a b s : C} (p : s --> a) (q : s --> b) (i : a --> s) (j : b --> s) :=
    dirprod (isBinaryProduct p q) (isBinaryCoproduct i j).
  
  Lemma isaprop_isBinarySum {C:precategory} {a b s : C} (p : s --> a) (q : s --> b) (i : a --> s) (j : b --> s) :
    isaprop (isBinarySum p q i j).
  Proof. prop_logic. Defined.

  Record BinarySum {C:precategory} (a b : C) := makeBinarySum {
      s ;
      p : s --> a ; q : s --> b ;
      i : a --> s ; j : b --> s ;
      is : isBinarySum p q i j
      }.

  Definition hasBinarySums (C:precategory) :=
    forall a b : C, mere (BinarySum a b).

End DirectSums.
