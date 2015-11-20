Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.CategoryTheory.precategories. (* get its coercions *)
Require Import UniMath.Ktheory.Precategories.
Local Open Scope cat.

Definition isUniversal {C:Precategory} {X:C==>SET} {c:C} (x:X c:hSet)
  := ∀ (c':C), isweq (λ f : c → c', # X f x).

Lemma isaprop_isUniversal {C:Precategory} {X:C==>SET} {c:C} (x:X c:hSet) :
  isaprop (isUniversal x).
Proof.
  intros. apply impred_isaprop; intro c'. apply isapropisweq.
Defined.

Definition Representation {C:Precategory} (X:C==>SET)
  := Σ (c:C) (x:X c:hSet), isUniversal x.

Definition makeRepresentation {C:Precategory} {X:C==>SET} {c:C} (x:X c:hSet) :
  (∀ (c':C), bijective (λ f : c → c', # X f x)) -> Representation X.
Proof.
  intros ? ? ? ? bij. exists c. exists x. intros c'.
  apply set_bijection_to_weq.
  - exact (bij c').
  - apply setproperty.
Defined.

Definition isRepresentable {C:Precategory} (X:C==>SET) := ∥ Representation X ∥.

Definition universalObject {C:Precategory} {X:C==>SET} (r:Representation X) : C
  := pr1 r.

Definition universalElement {C:Precategory} {X:C==>SET} (r:Representation X) :
  X (universalObject r) : hSet
  := pr1 (pr2 r).

Definition universalProperty {C:Precategory} {X:C==>SET} (r:Representation X) (c':C) :
  universalObject r → c' ≃ (X c' : hSet)
  := weqpair _ (pr2 (pr2 r) c').

Definition universalMap {C:Precategory} {X:C==>SET} (r:Representation X) (c':C) :
           (X c' : hSet) -> universalObject r → c'.
Proof.
  intros ? ? ? ? x'. exact (invmap (universalProperty r c') x').
Defined.

Definition mapUniqueness {C:Precategory} (X:C==>SET) (r : Representation X) (c':C)
           (f g:universalObject r → c') :
  # X f (universalElement r) = # X g (universalElement r) -> f = g.
Proof.
  intros ? ? ? ? ? ?. exact (invmaponpathsweq (universalProperty r c') f g).
Defined.

Lemma universalMapIdentity {C:Precategory} {X:C==>SET} (r:Representation X) :
  universalMap r (universalObject r) (universalElement r) = identity (universalObject r).
Proof.
  intros. apply mapUniqueness. intermediate_path (universalElement r).
  - exact (pr2 (pr1 (weqproperty (universalProperty _ _) _))).
  - now rewrite functor_id.
Defined.

Definition objectMap {C:Precategory} {X X':C==>SET} (r:Representation X) (r':Representation X') :
           (X' ⟶ X) -> (universalObject r → universalObject r').
Proof.
  intros ? ? ? ? ? p.
  exact (invmap (universalProperty r (universalObject r')) (p (universalObject r') (universalElement r'))).
Defined.

Definition objectMapUniqueness {C:Precategory} {X X':C==>SET}
           {r:Representation X} {r':Representation X'}
           (p : X ⟶ X')
           (f : universalObject r' → universalObject r) :
  (# X' f (universalElement r') = p (universalObject r) (universalElement r)) ->
  f = objectMap r' r p.
Proof. intros. now apply pathsweq1. Defined.

Definition objectMapIdentity {C:Precategory} {X:C==>SET} (r:Representation X) :
  objectMap r r (nat_trans_id X) = identity (universalObject r).
Proof. intros. apply universalMapIdentity. Defined.
