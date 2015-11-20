(* -*- coding: utf-8 -*- *)

Require Import UniMath.CategoryTheory.precategories UniMath.Foundations.Sets UniMath.Ktheory.Utilities UniMath.Ktheory.Precategories .
Require Import UniMath.Ktheory.InitialAndFinalObject.
Local Open Scope cat.

Definition ZeroObject (C:Precategory) := Σ z:ob C, isInitialObject C z × isTerminalObject C z.

Definition zero_opp (C:Precategory) : ZeroObject C -> ZeroObject C^op.
  intros C [z [i t]]. exact (z,,t,,i). Defined.

Definition zero_opp' (C:Precategory) : ZeroObject C^op -> ZeroObject C.
  intros ? X. exact (zero_opp C^op X). Defined.

Definition zero_object {C:Precategory} (z:ZeroObject C) : ob C := pr1  z.

Definition map_from    {C:Precategory} (z:ZeroObject C) := pr1(pr2 z).

Definition map_to      {C:Precategory} (z:ZeroObject C) := pr2(pr2 z).

Coercion zero_object : ZeroObject >-> ob.

Lemma initMapUniqueness {C:Precategory} (a:ZeroObject C) (b:ob C) (f:a→b) :
  f = thePoint (map_from a b).
Proof. intros. exact (uniqueness (map_from a b) f). Qed.

Lemma initMapUniqueness2 {C:Precategory} (a:ZeroObject C) (b:ob C) (f g:a→b) :
  f = g.
Proof. intros. intermediate_path (thePoint (map_from a b)).
  apply initMapUniqueness. apply pathsinv0. apply initMapUniqueness. Qed.

Definition hasZeroObject (C:Precategory) := ∥ ZeroObject C ∥.

Definition haszero_opp (C:Precategory) : hasZeroObject C -> hasZeroObject C^op.
  intros C. exact (hinhfun (zero_opp C)). Defined.

Lemma zeroObjectIsomorphy {C:Precategory} (a b:ZeroObject C) : iso a b.
Proof. intros.
       exact (theInitialObjectIsomorphy C a b (map_from a) (map_from b)). Defined.

Definition zeroMap' {C:Precategory} (a b:ob C) (o:ZeroObject C) :=
  thePoint (map_from o b) ∘ thePoint (map_to o a) : a → b.

Lemma path_right_composition {C:Precategory} (a b c:ob C) (g:a→b) (f f':b→c) :
  f = f' -> f ∘ g = f' ∘ g.
Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.

Lemma path_left_composition {C:Precategory} (a b c:ob C) (f:b→c) (g g':a→b) :
  g = g' -> f ∘ g = f ∘ g'.
Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.

Lemma zeroMapUniqueness {C:Precategory} (x y:ZeroObject C) (a b:ob C) :
  zeroMap' a b x = zeroMap' a b y.
Proof. intros. set (i := thePoint (map_to x a)).
  set (h := thePoint (map_from x y)). set (q := thePoint (map_from y b)).
  intermediate_path (q ∘ (h ∘ i)).
  { rewrite <- assoc. apply path_right_composition. apply uniqueness'. }
  { apply path_left_composition. apply uniqueness. } Qed.

Lemma zeroMap {C:Precategory} (a b:ob C): hasZeroObject C  ->  a → b.
Proof. intros ? ? ?.
       refine (squash_to_set _ _ _).
       { apply homset_property. }
       { apply zeroMap'. }
       { intros. apply zeroMapUniqueness. }
Defined.

Lemma zeroMap'_left_composition {C:Precategory}
      (z:ZeroObject C) (a b c:ob C) (f:b→c) :
  f ∘ zeroMap' a b z = zeroMap' a c z.
Proof. intros. unfold zeroMap'.
       intermediate_path ((f ∘ thePoint (map_from z b)) ∘ thePoint (map_to z a)).
       { apply pathsinv0. apply assoc. }
       { apply path_right_composition. apply initMapUniqueness. } Qed.

Lemma zeroMap_left_composition {C:Precategory}
      (a b c:ob C) (f:b→c) (h:hasZeroObject C) :
  f ∘ zeroMap a b h = zeroMap a c h.
Proof. intros ? ? ? ? ?. apply (@factor_dep_through_squash (ZeroObject C)).
       { intros. apply homset_property. }
       { intro z. apply zeroMap'_left_composition. }
Qed.
