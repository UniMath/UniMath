(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import RezkCompletion.precategories.
Import RezkCompletion.pathnotations.PathNotations.
Import Foundations.hlevel2.hSet.

Add LoadPath "." as Ktheory.
Require Import Ktheory.Utilities.

Local Notation "b <-- a" := (precategory_morphisms a b) (at level 50).
Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "f 'oo'  g" := (precategories.compose f g) (at level 50).
Local Notation "g 'o' f" := (precategories.compose f g) (at level 50).

Definition isiso {C:precategory} {a b:C} (f : a --> b) := total2 (is_inverse_in_precat f).

(** ** products *)

Module Products.

  (** *** terminal objects *)

  Definition isTerminalObject {C:precategory} (a:C) := forall (x:C), iscontr (a <-- x).

  Lemma isaprop_isTerminalObject {C:precategory} (a:C) : isaprop(isTerminalObject a).
  Proof. prop_logic. Qed.

  Definition isTerminalObjectProp {C:precategory} (a:C) := 
    hProppair (isTerminalObject a) (isaprop_isTerminalObject a) : hProp.

  Definition TerminalObject (C:precategory) := total2 (fun a:C => isTerminalObject a).

  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).

  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).

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

  Definition squashBinaryProducts (C:precategory) := forall a b : C, squash (BinaryProduct a b).

  Lemma isaprop_squashBinaryProducts (C:precategory) : isaprop (squashBinaryProducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryProductsProp (C:precategory) := 
    hProppair (squashBinaryProducts C) (isaprop_squashBinaryProducts _).

End Products.

(** ** coproducts *)

Module Coproducts.

  (** This module is obtained from the module Products by copying and then reversing arrows from --> to <--,
   reversing composition from o to oo, and changing various words. *)

  (** *** initial objects *)

  Definition isInitialObject {C:precategory} (a:C) := forall (x:C), iscontr (a --> x).

  Lemma initialObjectIsomorphy {C:precategory} (a b : C) : isInitialObject a -> isInitialObject b -> iso a b.
  Proof.
    intros maps_from_a_to maps_from_b_to. 
    exists (center (maps_from_a_to b)). 
    exists (center (maps_from_b_to a)).
    split. 
      path_via (center (maps_from_a_to a)). 
        apply contraction.
      apply pathsinv0. 
      apply contraction. 
    path_via (center (maps_from_b_to b)). 
      apply contraction.
    apply pathsinv0. 
    apply contraction.
  Defined.

  Lemma isaprop_isInitialObject {C:precategory} (a:C) : isaprop(isInitialObject a).
  Proof. prop_logic. Qed.

  Definition isInitialObjectProp {C:precategory} (a:C) := 
    hProppair (isInitialObject a) (isaprop_isInitialObject a) : hProp.

  Definition InitialObject (C:precategory) := total2 (fun a:C => isInitialObject a).

  Definition squashInitialObject (C:precategory) := squash (InitialObject C).

  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).

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

  Definition squashBinaryCoproducts (C:precategory) := forall a b : C, squash (BinaryCoproduct a b).

  Lemma isaprop_squashBinaryCoproducts (C:precategory) : isaprop (squashBinaryCoproducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryCoproductsProp (C:precategory) := 
    hProppair (squashBinaryCoproducts C) (isaprop_squashBinaryCoproducts _).

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
  (* Coercion zero_object : ZeroObject >->  *)

  Lemma initMapUniqueness {C:precategory} (a:ZeroObject C) (b:C) (f:zero_object a-->b) : f == center (init a b).
  Proof. intros. exact (contraction (init a b) f). Defined.

  Definition hasZeroObject (C:precategory) := squash (ZeroObject C).

  Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso (zero_object a) (zero_object b).
  Proof.
    exact (initialObjectIsomorphy (zero_object a) (zero_object b) (init a) (init b)).
  Defined.

  Definition zeroMap' {C:precategory} (zero:ZeroObject C) (a b:C) := center (init zero b) o center (term zero a) : a --> b.

  Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) : forall a b:C, zeroMap' x a b == zeroMap' y a b.
  Proof.
    intros. unfold zeroMap'. set (x0 := zero_object x). set (y0 := zero_object y). assert (h : x0 --> y0). exact (center (init x y0)).
    set (p := center (init x b)). set (i := center (term x a)). set (q := center (init y b)). set (j := center (term y a)).
    path_via (q o (h o i)). path_via ((q o h) o i). path_from (fun r : x0 --> b => r o i). apply pathsinv0.
    apply (contraction (init _ _)). apply (assoc C). path_from (fun s : a --> y0 => q o s). apply (contraction (term _ _)).
  Qed.

  Corollary zeroMapsUniqueness {C:precategory} (x y:ZeroObject C) : zeroMap' x == zeroMap' y.
  Proof.
    apply funextsec.
    intros t.
    apply funextsec.
    apply zeroMapUniqueness.
  Defined.

  Lemma zeroMap {C:precategory} : hasZeroObject C -> forall a b:C, a --> b.
  Proof.
    apply (squash_to_set _ (forall a b:C, a --> b) zeroMap').
      apply (impred 2).
      intro a. apply impred.
      intro b. apply isaset_hSet.
    exact zeroMapsUniqueness.
  Defined.
  
  Lemma goal1 {C:precategory} (h h':hasZeroObject C) : forall (a b:C), zeroMap h a b == zeroMap h' a b. 
  Proof. intros. path_from (fun h => zeroMap h a b). apply isaprop_squash. Qed.
  
  Lemma goal3 {C:precategory} (z:ZeroObject C) : forall (a b:C), zeroMap' z a b == zeroMap (squash_element z) a b. 
  Proof. intros. apply idpath. Qed.
  
  Lemma goal4 {C:precategory} (z:ZeroObject C) (h:hasZeroObject C) : forall (a b:C), zeroMap' z a b == zeroMap h a b. 
  Proof. intros. path_via (zeroMap (squash_element z) a b). apply idpath. apply goal1. Qed.

  Lemma goal5' {C:precategory} (z:ZeroObject C) : forall (b c:C) (f:b-->c), f  o  center (init z b) == center (init z c). 
  Proof. intros. apply (contraction (init z c)). Defined.

  Lemma goal10 {C:precategory} : forall (a b c:C) (f f':b-->c) (g:a-->b), f == f' -> f o g == f' o g.
  Proof. intros ? ? ? ? ? ? []. trivial. Defined.

  Definition left_compose {C:precategory} {a b:C} (c:C) (g:a-->b) (f:b-->c) := f o g.
  Definition right_compose {C:precategory} {c b:C} (f:b-->c) (a:C) (g:a-->b) := f o g.

  Lemma goal10a {C:precategory} : forall (a b c:C) (f f':b-->c) (g:a-->b), f == f' -> f o g == f' o g.
  Proof. intros ? ? ? ? ? ? p. path_from (left_compose c g). trivial. Defined.

  Lemma goal10' {C:precategory} : forall (a b c:C) (f:b-->c) (g g':a-->b), g == g' -> f o g == f o g'.
  Proof. intros ? ? ? ? ? ? []. apply idpath. Defined.

  Lemma goal5 {C:precategory} (z:ZeroObject C) : forall (a b c:C) (f:b-->c), f  o  zeroMap' z a b == zeroMap' z a c. 
  Proof. intros. unfold zeroMap'.
         path_via ((f o center (init z b)) o center (term z a)).
         apply pathsinv0.
         apply assoc.
         apply goal10.
         apply initMapUniqueness. Defined.

  Lemma goal2 {C:precategory} (h:hasZeroObject C) : forall (a b c:C) (f:b-->c), f  o  zeroMap h a b == zeroMap h a c. 
  Proof.
    intros.
    assert( i : isaprop (paths (f o zeroMap h a b) (zeroMap h a c) )). apply isaset_hSet.
    apply (@factor_through_squash (ZeroObject C) _ i).
     intro z.
     path_via (f  o  zeroMap' z a b).     
     path_from (right_compose f a).     
     apply pathsinv0.
     apply goal4.
     path_via (zeroMap' z a c).
     apply goal5.
     apply goal4.
    exact h.
  Defined.

  Lemma goal2' {C:precategory} (h:hasZeroObject C) : forall (a b c:C) (f:b-->c), f  o  zeroMap h a b == zeroMap h a c. 
  Proof.                        (* the proof term here is bigger than that of goal2 *)
    intros.
    assert( i : isaprop (paths (f o zeroMap h a b) (zeroMap h a c) )). apply isaset_hSet.
    apply (@factor_through_squash (ZeroObject C) _ i).
     intro z.
     assert( p : zeroMap' z a b == zeroMap h a b ). apply goal4. destruct p.
     assert( p : zeroMap' z a c == zeroMap h a c ). apply goal4. destruct p.
     unfold zeroMap'.
     assert( p : (f o center (init z b)) o center (term z a) == f o (center (init z b) o center (term z a)) ). apply assoc. destruct p.
     apply goal10.
     apply initMapUniqueness.
    exact h.
  Defined.

  (* the following definition is not right yet *)
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

  Definition squashBinarySums (C:precategory) :=
    forall a b : C, squash (BinarySum a b).

(**

  We are working toward definitions of "additive category" and "abelian
  category" as properties of a category, rather than as an added structure.
  That is the approach of Mac Lane in sections 18, 19, and 21 of :

  Duality for groups
  Bull. Amer. Math. Soc. Volume 56, Number 6 (1950), 485-516.
  http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045

 *)

End DirectSums.
