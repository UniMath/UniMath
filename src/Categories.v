(* -*- coding: utf-8-unix -*- *)

(* Set Printing All. *)

(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import Foundations.hlevel2.hSet.
Require Import Foundations.hlevel2.stnfsets.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.yoneda.
Import pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Add LoadPath "." as Ktheory.
Require Import Ktheory.Utilities.

Local Notation "b ← a" := (precategory_morphisms a b) (at level 50).
Local Notation "a → b" := (precategory_morphisms a b) (at level 50).
Local Notation "f ;; g" := (precategories.compose f g) (at level 50).
Local Notation "g ∘ f" := (precategories.compose f g) (at level 50).
Local Notation car := pr1.
Local Notation cadr := (fun x => pr1(pr2 x)).
Local Notation caddr := (fun x => pr1(pr2 (pr2 x))).
Local Notation cadddr := (fun x => pr1(pr2 (pr2 (pr2 x)))).
Local Notation cdr := pr2.
Local Notation cddr := (fun x => pr2(pr2 x)).
Local Notation cdddr := (fun x => pr2(pr2 (pr2 x))).
Local Notation cddddr := (fun x => pr2(pr2 (pr2 (pr2 x)))).
Notation "C '^op'" := (opp_precat C) (at level 3).

Definition assoc' (C : precategory) : 
   forall (a b c d : C) 
          (f : a → b)(g : b → c) (h : c → d),
                     h ∘ (g ∘ f) == (h ∘ g) ∘ f.
Proof. intros. apply pathReversal. apply assoc. Qed.

Definition precategory_pair (C : precategory_data) (i : is_precategory C)
  :  precategory
  := tpair is_precategory C i.

Definition category_pair (C : precategory) (i : is_category C)
  :  category
  := tpair is_category C i.

Unset Automatic Introduction.

Definition isiso {C:precategory} {a b:C} (f : a → b) := total2 (is_inverse_in_precat f).

(** ** products *)

Module Products.

  (** *** terminal objects *)

  Definition isTerminalObject {C:precategory} (a:C) := forall (x:C), iscontr (a ← x).

  Lemma terminalObjectIsomorphy {C:precategory} (a b : C) : isTerminalObject a -> isTerminalObject b -> iso a b.
  Proof.
    intros ? ? ?.
    intros map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_b_from_ a)).
    exists (the (map_to_a_from_ b)). 
    split. 
      intermediate (the (map_to_a_from_ a)). 
        apply uniqueness.
      apply uniqueness'. 
    intermediate (the (map_to_b_from_ b)). 
      apply uniqueness.
    apply uniqueness'.
  Defined.

  Lemma isaprop_isTerminalObject {C:precategory} (a:C) : isaprop(isTerminalObject a).
  Proof. prop_logic. Qed.

  Definition isTerminalObjectProp {C:precategory} (a:C) := 
    hProppair (isTerminalObject a) (isaprop_isTerminalObject a) : hProp.

  Definition TerminalObject (C:precategory) := total2 (fun a:C => isTerminalObject a).
  Definition terminalObject {C:precategory} (z:TerminalObject C) := car z.
  Definition terminalProperty {C:precategory} (z:TerminalObject C) := cdr z.

  Lemma isaprop_TerminalObject (C:category) : isaprop (TerminalObject C).
  Proof.
    intros.
    apply invproofirrelevance.
    intros a b.
    apply (total2_paths 
             (isotoid _ (pr2 C) 
                      (terminalObjectIsomorphy _ _ (terminalProperty a) (terminalProperty b)))).
    apply isaprop_isTerminalObject.
  Qed.

  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).

  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).

  (** *** binary products *)

  Definition isBinaryProduct {C:precategory} {a b p : C} (f : p → a) (g : p → b) :=
    forall p' (f' : p' → a) (g' : p' → b),
      iscontr ( total2 ( fun h => dirprod (f ∘ h == f') (g ∘ h == g'))).

  Lemma isaprop_isBinaryProduct {C:precategory} {a b p : C} (f : p → a) (g : p → b) : isaprop(isBinaryProduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryProductProp {C:precategory} {a b p : C} (f : p → a) (g : p → b) :=
    hProppair (isBinaryProduct f g) (isaprop_isBinaryProduct _ _).

  Definition BinaryProduct {C:precategory} (a b : C) := 
    total2 (fun p => 
    total2 (fun f : p → a => 
    total2 (fun g : p → b => 
                    isBinaryProduct f g))).

  Definition squashBinaryProducts (C:precategory) := forall a b : C, squash (BinaryProduct a b).

  Lemma isaprop_squashBinaryProducts (C:precategory) : isaprop (squashBinaryProducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryProductsProp (C:precategory) := 
    hProppair (squashBinaryProducts C) (isaprop_squashBinaryProducts _).

End Products.

(** ** coproducts *)

Module Coproducts.

  (** This module is obtained from the module Products by copying and then reversing arrows from → to ←,
   reversing composition from ∘ to ;;, and changing various words. *)

  (** *** initial objects *)

  Definition isInitialObject {C:precategory} (a:C) := forall (x:C), iscontr (a → x).

  Lemma initialObjectIsomorphy {C:precategory} (a b : C) : isInitialObject a -> isInitialObject b -> iso a b.
  Proof.
    intros ? ? ?.
    intros map_from_a_to map_from_b_to. 
    exists (the (map_from_a_to b)). 
    exists (the (map_from_b_to a)).
    split. 
      intermediate (the (map_from_a_to a)). 
        apply uniqueness.
      apply uniqueness'. 
    intermediate (the (map_from_b_to b)). 
      apply uniqueness.
    apply uniqueness'.
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

  Definition isBinaryCoproduct {C:precategory} {a b p : C} (f : p ← a) (g : p ← b) :=
    forall p' (f' : p' ← a) (g' : p' ← b),
      iscontr ( total2 ( fun h => dirprod (f ;; h == f') (g ;; h == g'))).

  Lemma isaprop_isBinaryCoproduct {C:precategory} {a b p : C} (f : p ← a) (g : p ← b) : isaprop(isBinaryCoproduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryCoproductProp {C:precategory} {a b p : C} (f : p ← a) (g : p ← b) :=
    hProppair (isBinaryCoproduct f g) (isaprop_isBinaryCoproduct _ _).

  Definition BinaryCoproduct {C:precategory} (a b : C) := 
    total2 (fun p => 
    total2 (fun f : p ← a => 
    total2 (fun g : p ← b => 
          isBinaryCoproduct f g))).

  Definition squashBinaryCoproducts (C:precategory) := forall a b : C, squash (BinaryCoproduct a b).

  Lemma isaprop_squashBinaryCoproducts (C:precategory) : isaprop (squashBinaryCoproducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryCoproductsProp (C:precategory) := 
    hProppair (squashBinaryCoproducts C) (isaprop_squashBinaryCoproducts _).

End Coproducts.

Module StandardCategories.

  Definition compose' { C : precategory_data } { a b c : C }
    (g : b → c) (f : a → b) : a → c.
  Proof.
    intros.
    exact (compose f g).
  Defined.

  Definition precat_paths_to_mor {C : precategory} (a b : ob C):
        a == b -> a → b.
  Proof.
    intros ? ? ? H.
    destruct H.
    exact (identity a).
  Defined.

  Lemma precat_paths_to_iso_mor {C : precategory} (a b : ob C) (e : a == b) :
    pr1 (precat_paths_to_iso a b e) == precat_paths_to_mor a b e.
  Proof.
    intros.
    destruct e.
    apply idpath.
  Defined.

  Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
    intros obj iobj.
    set (mor := @paths obj).
    assert(imor : forall i j : obj, isaset (mor i j)).
      intros.
      apply isaset_if_isofhlevel2.
      unfold isofhlevel.
      apply iobj.
    set (C := precategory_ob_mor_pair 
                obj 
                (fun i j : obj, hSetpair (mor i j) (imor i j))).
    set (identity' := (fun i : ob C => idpath i) : forall i:ob C, mor i i).
    set (compose' := (
           fun i j k : C => 
             fun f : mor i j =>
               fun g : mor j k => f @ g)
         : forall (i j k:ob C) (f:mor i j) (g:mor j k), mor i k ).
    set (D := precategory_data_pair C identity' compose').
    (*
        Notice how the next two proofs differ, due to the way the identity is 
        phrased.  The second one succeeds only because of a trivial
        intermediate step, but avoiding it seems hard.
     *)
    assert (right_identity :
           forall i j : D,
             forall f : mor i j, compose' _ _ _ (identity' i) f == f).
      intros. apply idpath.
    assert (left_identity :
           forall i j : D,
             forall f : i → j, compose f (identity j) == f).
      intros.
      intermediate (compose' _ _ _ f (identity' j)). trivial.
      apply pathscomp0rid.
    assert (associativity : forall (a b c d : C) 
                    (f : mor a b)(g : mor b c) (h : mor c d),
                     compose' _ _ _ f (compose' _ _ _ g h) == compose' _ _ _ (compose' _ _ _ f g) h).
      intros. destruct f. apply idpath.
    assert( iD : is_precategory D ).
      split. split. 
      apply right_identity. apply left_identity. apply associativity.
    set (E := precategory_pair D iD).
    clear right_identity. clear left_identity. clear associativity.
    assert(iE : is_category E).
      unfold is_category.
      intros.
      apply (gradth _ (morphism_from_iso _ a b)).
        intro. destruct x. apply idpath.
      intro.
      apply eq_iso.
      intermediate (precat_paths_to_mor a b (pr1 y)).
      apply precat_paths_to_iso_mor.
      assert (k : forall e, precat_paths_to_mor a b e == e).
        intro. destruct e. apply idpath.
      apply k.      
    set (F := category_pair E iE).
    exact F.
  Defined.

  Definition cat_n (n:nat) : category.
    (* discrete category on n objects *)
    intro.
    apply (path_groupoid (stn n)).
    apply hlevelntosn.
    apply isasetstn.
  Defined.

End StandardCategories.



Module DirectSums.

  Import Coproducts Products.

  Definition ZeroObject (C:precategory) := total2 ( fun 
               zero_object : C => dirprod (
                             isInitialObject zero_object) (
                             isTerminalObject zero_object) ).
  Definition zero_object {C:precategory} (z:ZeroObject C) := car  z.
  Definition map_from    {C:precategory} (z:ZeroObject C) := cadr z.
  Definition map_to      {C:precategory} (z:ZeroObject C) := cddr z.
  Coercion zero_object : ZeroObject >-> ob.

  Lemma initMapUniqueness {C:precategory} (a:ZeroObject C) (b:C) (f:a→b) : f == the (map_from a b).
  Proof. intros. exact (uniqueness (map_from a b) f). Qed.

  Lemma initMapUniqueness2 {C:precategory} (a:ZeroObject C) (b:C) (f g:a→b) : f == g.
  Proof.
   intros.
   intermediate (the (map_from a b)).
   apply initMapUniqueness.
   apply pathsinv0.
   apply initMapUniqueness.
  Qed.

  Definition hasZeroObject (C:precategory) := squash (ZeroObject C).

  Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso a b.
  Proof.
    intros.
    exact (initialObjectIsomorphy a b (map_from a) (map_from b)).
  Defined.

  Definition zeroMap' {C:precategory} (a b:C) (o:ZeroObject C) := the (map_from o b) ∘ the (map_to o a) : a → b.

  Lemma path_right_composition {C:precategory} : forall (a b c:C) (g:a→b) (f f':b→c), f == f' -> f ∘ g == f' ∘ g.
  Proof. intros ? ? ? ? ? ? ? []. apply idpath. Qed.

  Lemma path_left_composition {C:precategory} : forall (a b c:C) (f:b→c) (g g':a→b), g == g' -> f ∘ g == f ∘ g'.
  Proof. intros ? ? ? ? ? ? ? []. apply idpath. Qed.

  Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) : forall a b:C, zeroMap' a b x == zeroMap' a b y.
  Proof.
    intros.
    set(i := the (map_to x a)).
    set(h := the (map_from x y)).
    set(q := the (map_from y b)).
    intermediate (q ∘ (h ∘ i)). 
      intermediate ((q ∘ h) ∘ i). 
        apply path_right_composition.
        apply uniqueness'.
      apply assoc. 
    apply path_left_composition.
    apply uniqueness.
  Qed.

  Lemma zeroMap {C:precategory} (a b:C): hasZeroObject C  ->  a → b.
  Proof.
    intros ? ? ?.
    apply (squash_to_set (zeroMap' a b)).
    apply isaset_hSet.    
    intros. apply zeroMapUniqueness.
  Defined.

  Lemma zeroMap'_left_composition {C:precategory} (z:ZeroObject C) : forall (a b c:C) (f:b→c), f ∘ zeroMap' a b z == zeroMap' a c z. 
  Proof.
   intros. unfold zeroMap'.
   intermediate ((f ∘ the (map_from z b)) ∘ the (map_to z a)).
     apply assoc'.
   apply path_right_composition.
   apply initMapUniqueness.
  Qed.

  Lemma zeroMap_left_composition {C:precategory} (a b c:C) (f:b→c) (h:hasZeroObject C) : f ∘ zeroMap a b h == zeroMap a c h. 
  Proof.
    intros ? ? ? ? ?.
    apply (@factor_dep_through_squash (ZeroObject C)). intro. apply isaset_hSet.
    intro z.
    assert( g : forall (b:C), zeroMap' a b z == zeroMap a b (squash_element z) ). trivial.
    destruct (g b).
    destruct (g c).
    apply zeroMap'_left_composition.
  Qed.

  (* the following definition is not right yet *)
  Definition isBinarySum {C:precategory} {a b s : C} (p : s → a) (q : s → b) (i : a → s) (j : b → s) :=
    dirprod (isBinaryProduct p q) (isBinaryCoproduct i j).
  
  Lemma isaprop_isBinarySum {C:precategory} {a b s : C} (p : s → a) (q : s → b) (i : a → s) (j : b → s) :
    isaprop (isBinarySum p q i j).
  Proof. prop_logic. Qed.

  Definition BinarySum {C:precategory} (a b : C) := 
                    total2 (fun 
      s          => total2 (fun 
      p : s → a  => total2 (fun  
      q : s → b  => total2 (fun 
      i : a → s  => total2 (fun  
      j : b → s  => 
          isBinarySum p q i j ))))).

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

