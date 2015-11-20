Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.Elements. (* should not be needed *)
Local Open Scope cat.

Definition Representation {C:Precategory} (X:C==>SET)
  := Σ (c:C) (x:set_to_type (X c)), ∀ (c':C), isweq (λ f : c → c', # X f x).

Definition makeRepresentation {C:Precategory} (X:C==>SET) (c:C) (x:set_to_type (X c)) :
  (∀ (c':C), bijective (λ f : c → c', # X f x)) -> Representation X.
Proof.
  intros ? ? ? ? bij. exists c. exists x. intros.
  apply bijection_to_weq, bij.
Defined.

Definition isRepresentable {C:Precategory} (X:C==>SET) := ∥ Representation X ∥.

Definition universalObject {C:Precategory} {X:C==>SET} (r:Representation X) : C
  := pr1 r.

Definition universalElement {C:Precategory} {X:C==>SET} (r:Representation X) :
  set_to_type (X (universalObject r))
  := pr1 (pr2 r).

Definition universalProperty {C:Precategory} {X:C==>SET} (r:Representation X) (c':C) :
  universalObject r → c' ≃ set_to_type (X c')
  := weqpair _ (pr2 (pr2 r) c').

Definition universalMap {C:Precategory} {X:C==>SET} (r:Representation X) (c':C) :
           set_to_type(X c') -> universalObject r → c'.
Proof.
  intros ? ? ? ? x'. exact (invmap (universalProperty r c') x').
Defined.

Definition mapUniqueness {C:Precategory} (X:C==>SET) (r : Representation X) (c':C)
           (f g:universalObject r → c') : # X f (universalElement r) = # X g (universalElement r) -> f = g.
Proof.
  intros ? ? ? ? ? ?. exact (invmaponpathsweq (universalProperty r c') f g).
Defined.

Definition objectMap {C:Precategory} {X X':C==>SET} (r:Representation X) (r':Representation X') :
           (X' ⟶ X) -> (universalObject r → universalObject r').
Proof.
  intros ? ? ? ? ? p.
  exact (invmap (universalProperty r (universalObject r')) (p (universalObject r') (universalElement r'))).
Defined.

Definition objectMapUniqueness {C:Precategory} {X X':C==>SET}
           (r:Representation X) (r':Representation X')
           (p : X ⟶ X')
           (f : universalObject r' → universalObject r)
           (e : # X' f (universalElement r') = p (universalObject r) (universalElement r))
  : f = objectMap r' r p.
Proof. intros. now apply pathsweq1. Defined.

Definition objectMapIdentity {C:Precategory} {X:C==>SET} (r:Representation X) :
  identity (universalObject r) = objectMap r r (nat_trans_id X).
Proof.
Admitted.
