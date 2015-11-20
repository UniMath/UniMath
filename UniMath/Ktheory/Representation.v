Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.CategoryTheory.precategories. (* get its coercions *)
Require Import UniMath.Ktheory.Precategories.
Set Automatic Introduction.
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
  intros bij. exists c. exists x. intros c'. apply set_bijection_to_weq.
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
  := weqpair _ (pr2 (pr2 r) _).

Definition universalMap {C:Precategory} {X:C==>SET} {r:Representation X} {c':C} :
  (X c' : hSet) -> universalObject r → c'
  := invmap (universalProperty _ _).

Definition mapUniqueness {C:Precategory} (X:C==>SET) (r : Representation X) (c':C)
           (f g:universalObject r → c') :
  # X f (universalElement r) = # X g (universalElement r) -> f = g
  := invmaponpathsweq (universalProperty _ _) _ _.

Lemma universalMapIdentity {C:Precategory} {X:C==>SET} (r:Representation X) :
  universalMap (universalElement r) = identity _.
Proof.
  intros. apply mapUniqueness. intermediate_path (universalElement r).
  - exact (pr2 (pr1 (weqproperty (universalProperty _ _) _))).
  - now rewrite functor_id.
Defined.

Definition embeddingRepresentability {C D:Precategory}
           {i:C==>D} (emb:fully_faithful i) {Y:D==>SET} (s:Representation Y) :
           (Σ c, universalObject s = i c) -> Representation (Y □ i).
Proof.
  intros ce. exists (pr1 ce).
  exists (transportf (λ d, Y d : hSet) (pr2 ce) (universalElement s)).
  intro c'. apply (twooutof3c (# i) (λ g, # Y g _)).
  - apply emb.
  - induction (pr2 ce). exact (weqproperty (universalProperty _ _)).
Defined.

Definition objectMap {C:Precategory} {X X':C==>SET} (r:Representation X) (r':Representation X') :
  (X' ⟶ X) -> (universalObject r → universalObject r')
  := λ p, universalMap (p _ (universalElement r')).

Definition objectMapUniqueness {C:Precategory} {X X':C==>SET}
           {r:Representation X} {r':Representation X'}
           (p : X ⟶ X')
           (f : universalObject r' → universalObject r) :
  (# X' f (universalElement r') = p (universalObject r) (universalElement r)) ->
  f = objectMap r' r p
  := pathsweq1 (universalProperty _ _) _ _.

Definition objectMapIdentity {C:Precategory} {X:C==>SET} (r:Representation X) :
  objectMap r r (nat_trans_id X) = identity (universalObject r).
Proof. intros. apply universalMapIdentity. Defined.
