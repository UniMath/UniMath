(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import RezkCompletion.precategories Foundations.hlevel2.hSet Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Primitive.
Import Utilities.Notation Precategories.Notation
       pathnotations.PathNotations
       Primitive.TerminalObject Primitive.InitialObject.
Definition ZeroObject (C:precategory) := total2 ( fun 
             z : ob C => dirprod (
                 isInitialObject C z) (
                 isTerminalObject C z) ).
Definition zero_opp (C:precategory) : ZeroObject C -> ZeroObject C^op.
  intros C [z [i t]]. exact (z ,, (t ,, i)). Defined.
Definition zero_opp' (C:precategory) : ZeroObject C^op -> ZeroObject C.
  intros ? X. exact (zero_opp C^op X). Defined.
Definition zero_object {C:precategory} (z:ZeroObject C) : ob C := pr1  z.
Definition map_from    {C:precategory} (z:ZeroObject C) := pr1(pr2 z).
Definition map_to      {C:precategory} (z:ZeroObject C) := pr2(pr2 z).
Coercion zero_object : ZeroObject >-> ob.
Lemma initMapUniqueness {C:precategory} (a:ZeroObject C) (b:ob C) (f:a→b) :
  f == the (map_from a b).
Proof. intros. exact (uniqueness (map_from a b) f). Qed.
Lemma initMapUniqueness2 {C:precategory} (a:ZeroObject C) (b:ob C) (f g:a→b) :
  f == g.
Proof. intros. intermediate_path (the (map_from a b)).
  apply initMapUniqueness. apply pathsinv0. apply initMapUniqueness. Qed.
Definition hasZeroObject (C:precategory) := squash (ZeroObject C).
Definition haszero_opp (C:precategory) : hasZeroObject C -> hasZeroObject C^op.
  intros C. exact (hinhfun (zero_opp C)). Defined.
Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso a b.
Proof. intros. 
       exact (theInitialObjectIsomorphy C a b (map_from a) (map_from b)). Defined.
Definition zeroMap' {C:precategory} (a b:ob C) (o:ZeroObject C) := 
  the (map_from o b) ∘ the (map_to o a) : a → b.
Lemma path_right_composition {C:precategory} (a b c:ob C) (g:a→b) (f f':b→c) :
  f == f' -> f ∘ g == f' ∘ g.
Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.
Lemma path_left_composition {C:precategory} (a b c:ob C) (f:b→c) (g g':a→b) :
  g == g' -> f ∘ g == f ∘ g'.
Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.
Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) (a b:ob C) :
  zeroMap' a b x == zeroMap' a b y.
Proof. intros. set (i := the (map_to x a)).
  set (h := the (map_from x y)). set (q := the (map_from y b)).
  intermediate_path (q ∘ (h ∘ i)).
  { rewrite <- assoc. apply path_right_composition. apply uniqueness'. }
  { apply path_left_composition. apply uniqueness. } Qed.
Lemma zeroMap {C:precategory} (a b:ob C): hasZeroObject C  ->  a → b.
Proof. intros ? ? ?. 
       refine (squash_to_set _ _ _).
       { apply setproperty. }
       { apply zeroMap'. }
       { intros. apply zeroMapUniqueness. } Defined.
Lemma zeroMap'_left_composition {C:precategory} 
      (z:ZeroObject C) (a b c:ob C) (f:b→c) :
  f ∘ zeroMap' a b z == zeroMap' a c z. 
Proof. intros. unfold zeroMap'. 
       intermediate_path ((f ∘ the (map_from z b)) ∘ the (map_to z a)).
       { apply pathsinv0. apply assoc. }
       { apply path_right_composition. apply initMapUniqueness. } Qed.
Lemma zeroMap_left_composition {C:precategory} 
      (a b c:ob C) (f:b→c) (h:hasZeroObject C) : 
  f ∘ zeroMap a b h == zeroMap a c h. 
Proof. intros ? ? ? ? ?. apply (@factor_dep_through_squash (ZeroObject C)). 
       intro. apply setproperty. intro z. apply zeroMap'_left_composition. Qed.
