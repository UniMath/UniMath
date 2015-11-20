(* -*- coding: utf-8 -*- *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.ZeroObject
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Precategories.
Local Open Scope cat.

Definition zerocomp_type {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> Type.
Proof. intros ? ? ? ? ? x.
  exact (Σ g:Hom C d x, g ∘ f = zeroMap c x z). Defined.

Definition zerocomp_type_isaset {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ∀ x:ob C, isaset (zerocomp_type z f x).
Proof. intros ? ? ? ? ? x.
  apply (isofhleveltotal2 2).
  { apply homset_property. }
  { intro g.
    assert( t:isofhlevel 3 (Hom C c x) ).
    { apply hlevelntosn.  apply homset_property. }
    exact (t _ _).            (* why doesn't apply t work here? *)
    } Qed.

Definition zerocomp_set {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> ob SET.
Proof. intros ? ? ? ? ? x.
  exact (zerocomp_type z f x,, zerocomp_type_isaset z f x). Defined.

Definition zerocomp_map {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ∀ x y:ob C,
    Hom C x y -> (zerocomp_set z f x : hSet) -> (zerocomp_set z f y : hSet).
Proof. intros ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc. rewrite s.
       apply zeroMap_left_composition. Defined.

Definition zerocomp_data {C:Precategory}  (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  functor_data (Precategories.Precategory_obmor C) (Precategories.Precategory_obmor SET).
Proof. intros.
       exact (zerocomp_set z f,, zerocomp_map z f). Defined.

Definition zerocomp {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d):C ==> SET.
  intros. exists (zerocomp_data z f). split.
  { intros x. apply funextsec; intros [r rf0].
    apply subtypeEquality.
    { intro; apply homset_property. }
    apply id_right. }
  { intros w x y t u. apply funextsec. intros [r rf0].
    apply subtypeEquality.
    { intro; apply homset_property. }
    apply assoc. }
Defined.

Definition Cokernel {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
  Representation (zerocomp z f).

Definition Kernel (C:Precategory) (z:hasZeroObject C) (c d:ob C) (f:c → d) :=
  Representation (zerocomp (haszero_opp C z) f).
