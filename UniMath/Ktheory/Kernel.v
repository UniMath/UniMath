(* -*- coding: utf-8 -*- *)

Require Import 
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.ZeroObject.
Require Import UniMath.Ktheory.Utilities.
Require UniMath.Ktheory.Representation.
Import UniMath.Ktheory.Precategories.Notation.
Definition zerocomp_type {C:precategory} (hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> Type.
Proof. intros ? ? ? ? ? ? x.
  exact (total2( fun g:Hom d x => g ∘ f = zeroMap hs c x z)). Defined.
Definition zerocomp_type_isaset {C: precategory}(hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  forall x:ob C, isaset (zerocomp_type hs z f x).
Proof. intros ? ? ? ? ? ? x.
  apply (isofhleveltotal2 2).
  { apply hs. }
  { intro g.  
    assert( t:isofhlevel 3 (Hom c x) ).
    { apply hlevelntosn.  apply hs. }
    exact (t _ _).            (* why doesn't apply t work here? *)
    } Qed.  
Definition zerocomp_set {C:precategory}(hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  ob C -> ob SET.
Proof. intros ? ? ? ? ? ? x.
  exact (zerocomp_type _ z f x,, zerocomp_type_isaset hs z f x). Defined.
Definition zerocomp_map {C:precategory}(hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  forall x y:ob C, Hom x y ->
  set_to_type (zerocomp_set hs z f x) -> set_to_type (zerocomp_set hs z f y).
Proof. intros ? ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc. rewrite s.
       apply zeroMap_left_composition. Defined.
Definition zerocomp_data {C:precategory} (hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
Proof. intros. 
       exact (zerocomp_set hs z f,, zerocomp_map hs z f). Defined.
Definition zerocomp {C:precategory}(hs: has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d):C ==> SET.
  intros. exists (zerocomp_data hs z f). split.
  { intros x. apply funextsec; intros [r rf0].
    apply (Utilities.pair_path_props (id_right _ _ _ r)). 
    intro g. apply hs. }
  { intros w x y t u. apply funextsec. intros [r rf0].
    apply (Utilities.pair_path_props (assoc _ _ _ _ _ r t u)).
    intro g. apply hs. } Defined.
Definition Cokernel {C:precategory}(hs:has_homsets C) (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
  Representation.Data (zerocomp hs z f).
Definition Kernel (C:precategory)(hs: has_homsets C) (z:hasZeroObject C) (c d:ob C) (f:c → d) :=
  Representation.Data (zerocomp (Precategories.has_homsets_opp_precat _ hs ) (haszero_opp C z) f).
