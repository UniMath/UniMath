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
Local Notation "f ~ g" := (Foundations.Generalities.uu0.homot f g) (at level 51).

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

Definition squash (X:UU) := forall P:UU, isaprop P -> (X -> P) -> P. (* compare with ishinh_UU *)

Definition squash_dep (X:UU) := forall P:X -> UU, (forall x:X, isaprop (P x)) -> (forall x:X, P x) -> squash (total2 P).

Definition squash_element (X:UU) : X -> squash X.
Proof.
  intros x P i f.
  apply f.
  assumption.
Defined.

Definition squash_dep_element (X:UU) : X -> squash_dep X.
Proof.
  intros x P h s.
  apply squash_element.
  exists x.
  apply s.
Defined.

Lemma isaprop_squash (X:UU) : isaprop (squash X).
Proof. prop_logic. Qed.

Lemma isaprop_squash_dep (X:UU) : isaprop (squash_dep X).
Proof. 
  apply (impred 1).
  intro S.
  apply impred.
  intro is.
  apply impred.  
  intro s.  
  apply isaprop_squash.
Defined.

Lemma factor_through_squash {X Q:UU} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof.
  intros i f h.  apply h.  assumption.  assumption.
Defined.

Lemma lift_through_squash_dep {X:UU} {Q : squash_dep X -> UU} : 
  (forall y : squash_dep X, isaprop (Q y)) 
  -> (forall x:X, Q (squash_dep_element X x))
  -> (forall y : squash_dep X, Q y).
Proof.
  intros is q y.
  set (S := funcomp (squash_dep_element X) Q).
  apply (y S).
    intro x.
    apply is.
  apply q.
  apply is.
  intros [x p].
  set (y' := squash_dep_element _ x).
  assert(e : y' == y).
  apply isaprop_squash_dep.
  assert(t : Q y').
  exact p.
  apply (transportf _ e).  
  assumption.
Defined.

Lemma factor_through_squash_dep {X Q:UU} : isaprop Q -> (X -> Q) -> (squash_dep X -> Q).
Proof.
  intros is q y.
  unfold squash_dep in y.
  apply (y (fun _ => Q)).
  intros x.
  assumption.
  assumption.
  assumption.
  intros [_ q'].
  assumption.
Defined.

Lemma squashes_agree {X:UU} : weq (squash X) (squash_dep X).
Proof.
  unfold weq.
  exists (factor_through_squash (isaprop_squash_dep X) (squash_dep_element X)).
  apply (gradth _ (factor_through_squash_dep (isaprop_squash X) (squash_element X))).
  intro x.
  apply (isaprop_squash X).
  intro y.
  apply (isaprop_squash_dep X).
Defined.

Lemma squash_dep_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash_dep X -> S) : 
  funcomp (squash_dep_element X) g ~ funcomp (squash_dep_element X) g' 
  -> g ~ g'.
Proof.
  intros h.
  set ( Q := fun y => g y == g' y ).
  assert ( iq : forall y, isaprop (Q y) ).
    intros y. apply ip.
  intros y.
  apply (lift_through_squash_dep iq h).
Defined.

Lemma squash_dep_map_epi {X S:UU} (ip : isaset S) (g g' : squash_dep X -> S) : 
  funcomp (squash_dep_element X) g == funcomp (squash_dep_element X) g' 
  -> g == g'.
Proof.
  exact (fun e => funextfunax _ _ _ _ (squash_dep_map_uniqueness ip _ _ (fun x => maponpaths (fun q : X -> S => q x) e))).
Defined.

Lemma isweq_factor_through_squash (X P:UU) (i : isaprop P) : isweq (@factor_through_squash X P i).
Proof.
  set ( comp := (fun k : squash X -> P => funcomp (squash_element X) k) ).
  apply (gradth _ comp).
  intro f.
  apply funextfunax.
  intro x.
  apply idpath.
  intro g.
  apply funextfunax.
  intro h.
  admit.
Defined.

Definition squash_factoring {X Y:UU} (f : X -> Y) := total2 (fun g : squash X -> Y => f ~ funcomp (squash_element X) g).

Definition isaprop_squash_factoring {X Y:UU} (f : X -> Y) : isaprop (squash_factoring f).
Proof.
  unfold isaprop.  
  unfold isofhlevel.
  intros [g h] [g' h'].
  assert( t : g == g' ).
  admit.
  admit.
Qed.

Lemma squash_to_type (X Y:UU) : forall f : X -> Y, (forall x x' : X, f x == f x') -> squash_factoring f.
  intros f e.
  set ( h := factor_through_squash (isaprop_squash_factoring f) 
                         (fun x => tpair (fun g : squash X -> Y => f ~ funcomp (squash_element X) g) 
                                         (fun _ => f x) (fun x' => e x' x))
           : squash X -> squash_factoring f ).
  exists (fun r => (pr1 (h r)) r).
  intro x.
  unfold h.
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

  Definition squashInitialObject (C:precategory) := squash (InitialObject C).

  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).

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

  Definition squashZeroObject (C:precategory) := squash (ZeroObject C).

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

  Definition zeroMap2 {C:precategory} {mere_zero:squashZeroObject C} (a b:C) : a --> b.
  Proof.
    unfold squashZeroObject in mere_zero.
    unfold squash in mere_zero.
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

  Definition squashBinarySums (C:precategory) :=
    forall a b : C, squash (BinarySum a b).

End DirectSums.
