(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import RezkCompletion.precategories.
Import RezkCompletion.pathnotations.PathNotations.
Import Foundations.hlevel2.hSet.

Local Notation "b <-- a" := (precategory_morphisms a b) (at level 50).
Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "f 'oo'  g" := (precategories.compose f g) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).

Definition pathscomp0' {T:UU} {a b c:T} : a == b -> b == c -> a == c.
Proof. intros e1 e2. 
  destruct e2. (* compare to Foundations.uu0.pathscomp0, which destructs e1, instead *)
  assumption. 
Defined.

Ltac path_via  x   := apply (@pathscomp0  _  _ x).
Ltac path_via' x   := apply (@pathscomp0' _  _ x).
Ltac path_via2 x y := apply (@pathscomp0  _  _ x _  _ (@pathscomp0 _  _ y _  _ _)).
Ltac path_from f := apply (@maponpaths _ _ f).

Ltac prop_logic := 
  simpl;
  repeat (try (apply isapropdirprod); try (apply isapropishinh); apply impred ; intro); 
  try (apply isapropiscontr);
  try assumption.

Global Opaque isapropiscontr isapropishinh.

Definition has (X:UU) := forall P:UU, isaprop P -> (X -> P) -> P. (* compare with ishinh_UU *)

Lemma isaprop_has (X:UU) : isaprop(has X).
Proof. prop_logic. Qed.

Definition has2 (X:UU) := setquot (fun _ _ : X => htrue).
Lemma isaprop_has2 (X:UU) : isaprop(has2 X).
Proof.
  intros [p i] [q j].
  unfold hsubtypes in *.
  assert(u : p == q).
  apply funextfunax.  
  unfold iseqclass in *.
  admit.
  admit.
Defined.

Lemma has_to_prop (X P:UU) : isaprop P -> (X -> P) -> (has X -> P).
Proof.
  intros i f h.  apply h.  assumption.  assumption.
Defined.

Lemma has_to_set (X S:UU) : isaset S -> forall f : X -> S, (forall x x' : X, f x == f x') -> (has X -> S).
  intros i f e h.
  assert (q : X -> has X -> S).
  intro x.
  set (P := total2 (fun s => f x == s)).
  assert (c : iscontr P).
  unfold iscontr.
  admit.
  assert (d : isaprop P).
  apply isapropifcontr.
  assumption.
  assert (t : has X -> P).
  apply has_to_prop.
  assumption.
  intro x'.
  exact (tpair _ (f x') (e x x')).
  intro h'.
  exact (pr1 (t h')).
  admit.
Defined.

Definition isiso {C:precategory} {a b:C} (f : a --> b) := total2 (is_inverse_in_precat f).

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

  Definition hasInitialObject (C:precategory) := has (InitialObject C).

  Definition hasInitialObjectProp (C:precategory) := 
    hProppair (hasInitialObject C) (isaprop_has _).

  (** *** binary products *)

  Definition isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) :=
    forall p' (f' : p' --> a) (g' : p' --> b),
      iscontr ( total2 ( fun h => dirprod (f o h == f') (g o h == g'))).

  Lemma isaprop_isBinaryProduct {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) : isaprop(isBinaryProduct f g).
  Proof. prop_logic. Qed.

  Lemma binaryProductIsomorphy {C:precategory} {a b : C}
     (p :C) (f : p --> a) (g : p --> b) (ip : isBinaryProduct f  g )
     (p':C) (f': p'--> a) (g': p'--> b) (ip': isBinaryProduct f' g') :
     total2 (fun h : p --> p' => dirprod (dirprod (f' o h == f) (g' o h == g)) (isiso h)).
  Proof.
    set (k := ip' _ f g).
    set (k':= ip _ f' g').
    exists (pr1 (pr1 k)).
    split.
    split.
    exact (pr1 (pr2 (pr1 k))).
    exact (pr2 (pr2 (pr1 k))).
    exists (pr1 (pr1 k')).
    split.
    path_via (pr1 (pr1 (ip _ f g))).
    admit. admit. admit.
  Defined.

  Definition isBinaryProductProp {C:precategory} {a b p : C} (f : p --> a) (g : p --> b) :=
    hProppair (isBinaryProduct f g) (isaprop_isBinaryProduct _ _).

  Definition BinaryProduct {C:precategory} (a b : C) := 
    total2 (fun p => 
              total2 (fun f : p --> a => 
                        total2 (fun g : p --> b => 
                                  isBinaryProduct f g))).

  Definition hasBinaryProducts (C:precategory) := forall a b : C, has (BinaryProduct a b).

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

  Definition hasTerminalObject (C:precategory) := has (TerminalObject C).

  Definition hasTerminalObjectProp (C:precategory) := 
    hProppair (hasTerminalObject C) (isaprop_has _).

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

  Definition hasBinaryCoproducts (C:precategory) := forall a b : C, has (BinaryCoproduct a b).

  Lemma isaprop_hasBinaryCoproducts (C:precategory) : isaprop (hasBinaryCoproducts C).
  Proof. prop_logic. Qed.

  Definition hasBinaryCoproductsProp (C:precategory) := 
    hProppair (hasBinaryCoproducts C) (isaprop_hasBinaryCoproducts _).

End Coproducts.

Module DirectSums.

  Import Coproducts Products.

  Record ZeroObject (C:precategory) := makeZeroObject { 
      zero_object : C ; 
      init : isInitialObject zero_object ; 
      term : isTerminalObject zero_object }.
  Implicit Arguments zero_object [C].
  Implicit Arguments init [C].
  Implicit Arguments term [C].

  Definition hasZeroObject (C:precategory) := has (ZeroObject C).

  Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso (zero_object a) (zero_object b).
  Proof.
    exact (initialObjectIsomorphy (zero_object a) (zero_object b) (init a) (init b)).
  Defined.

  Definition zeroMap {C:precategory} (zero:ZeroObject C) (a b:C) := pr1 (init zero b) o pr1 (term zero a) : a --> b.

  Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) : forall a b:C, zeroMap x a b == zeroMap y a b.
  Proof.
    intros. unfold zeroMap. set (x0 := zero_object x). set (y0 := zero_object y). assert (h : x0 --> y0). exact (pr1 (init x y0)).
    set (p := pr1 (init x b)). set (i := pr1 (term x a)). set (q := pr1 (init y b)). set (j := pr1 (term y a)).
    path_via (q o (h o i)). path_via ((q o h) o i). path_from (fun r : x0 --> b => r o i). apply pathsinv0.
    apply (pr2 (init _ _)). apply (assoc C). path_from (fun s : a --> y0 => q o s). apply (pr2 (term _ _)).
  Qed.

  Definition zeroMap2 {C:precategory} {mere_zero:hasZeroObject C} (a b:C) : a --> b.
  Proof.
    unfold hasZeroObject in mere_zero.
    unfold has in mere_zero.
    admit.
  Defined.
  
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
    forall a b : C, has (BinarySum a b).

End DirectSums.
