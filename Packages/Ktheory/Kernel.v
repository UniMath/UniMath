(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.ZeroObject.
Require Ktheory.Utilities Ktheory.Representation.
Import RezkCompletion.pathnotations.PathNotations 
       Utilities.Notation Precategories.Notation.
Definition zerocomp_type {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> Type.
Proof. intros ? ? ? ? ? x.
  exact (total2( fun g:Hom d x => g ∘ f == zeroMap c x z)). Defined.
Definition zerocomp_type_isaset {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  forall x:ob C, isaset (zerocomp_type z f x).
Proof. intros ? ? ? ? ? x.
  apply (isofhleveltotal2 2).
  { apply setproperty. }
  { intro g.  
    assert( t:isofhlevel 3 (Hom c x) ).
    { apply hlevelntosn.  apply setproperty. }
    exact (t _ _).            (* why doesn't apply t work here? *)
    } Qed.  
Definition zerocomp_set {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> ob SET.
Proof. intros ? ? ? ? ? x.
  exact (zerocomp_type z f x,, zerocomp_type_isaset z f x). Defined.
Definition zerocomp_map {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  forall x y:ob C, Hom x y ->
  set_to_type (zerocomp_set z f x) -> set_to_type (zerocomp_set z f y).
Proof. intros ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc. rewrite s.
       apply zeroMap_left_composition. Defined.
Definition zerocomp_data {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
Proof. intros. 
       exact (zerocomp_set z f,, zerocomp_map z f). Defined.
Definition zerocomp {C} (z:hasZeroObject C) {c d:ob C} (f:c → d):C ==> SET.
  intros. exists (zerocomp_data z f). split.
  { intros x. apply funextsec; intros [r rf0].
    apply (Utilities.pair_path_props (id_right _ _ _ r)). 
    intro g. apply setproperty. }
  { intros w x y t u. apply funextsec. intros [r rf0].
    apply (Utilities.pair_path_props (assoc _ _ _ _ _ r t u)).
    intro g. apply setproperty. } Defined.
Definition Cokernel {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
  Representation.Data (zerocomp z f).
Definition Kernel C (z:hasZeroObject C) (c d:ob C) (f:c → d) :=
  Representation.Data (zerocomp (haszero_opp C z) f).

