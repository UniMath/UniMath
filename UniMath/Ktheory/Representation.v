Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.CategoryTheory.precategories. (* get its coercions *)
Require Import UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.Bifunctor.
Set Automatic Introduction.
Local Open Scope cat.

Definition isUniversal {C:Precategory} {X:[C,SET]} {c:C} (x:X ⇒ c)
  := ∀ (c':C), isweq (λ f : c → c', f ⟳ x).

Lemma isaprop_isUniversal {C:Precategory} {X:[C,SET]} {c:C} (x:X ⇒ c) :
  isaprop (isUniversal x).
Proof. intros. apply impred_isaprop; intro c'. apply isapropisweq. Defined.

Definition Representation {C:Precategory} (X:[C,SET]) : UU
  := Σ (c:C) (x:X ⇒ c), isUniversal x.

Definition isRepresentable {C:Precategory} (X:[C,SET]) := ∥ Representation X ∥.

Lemma isaprop_Representation {C:category} (X:[C,SET]) :
  isaprop (@Representation C X).
Proof.

Abort.

(* categories of functors with representations *)

Definition RepresentedFunctor (C:Precategory) : Precategory
  := @categoryWithStructure [C,SET] Representation.

Definition toRepresentation {C:Precategory} (X : RepresentedFunctor C) :
  Representation (pr1 X)
  := pr2 X.

Definition RepresentableFunctor (C:Precategory) : Precategory
  := @categoryWithStructure [C,SET] isRepresentable.

Definition toRepresentableFunctor {C:Precategory} :
  RepresentedFunctor C ==> RepresentableFunctor C :=
  functorWithStructures (λ c, hinhpr).

(* make a representation of a functor *)

Definition makeRepresentation {C:Precategory} {X:[C,SET]} {c:C} (x:X ⇒ c) :
  (∀ (c':C), bijective (λ f : c → c', f ⟳ x)) -> Representation X.
Proof.
  intros bij. exists c. exists x. intros c'. apply set_bijection_to_weq.
  - exact (bij c').
  - apply setproperty.
Defined.

(* universal aspects of represented functors *)

Definition universalObject {C:Precategory} {X:[C,SET]} (r:Representation X) : C
  := pr1 r.

Definition universalElement {C:Precategory} {X:[C,SET]} (r:Representation X) :
  X ⇒ universalObject r
  := pr1 (pr2 r).

Coercion universalElement : Representation >-> pr1hSet.

Definition universalProperty {C:Precategory} {X:[C,SET]} (r:Representation X) (c:C) :
  universalObject r → c ≃ X ⇒ c
  := weqpair (λ f : universalObject r → c, f ⟳ r)
             (pr2 (pr2 r) c).

Definition universalMap {C:Precategory} {X:[C,SET]} (r:Representation X) {c:C} :
  X ⇒ c -> universalObject r → c
  := invmap (universalProperty _ _).

Notation "x // r" := (universalMap r x) (at level 50, left associativity) : cat.

Definition universalMapProperty {C:Precategory} {X:[C,SET]} {r:Representation X}
      {c:C} (x : X ⇒ c) :
  (x // r) ⟳ r = x
  := homotweqinvweq (universalProperty r c) x.

Definition mapUniqueness {C:Precategory} (X:[C,SET]) (r : Representation X) (c:C)
           (f g:universalObject r → c) :
  f ⟳ r = g ⟳ r -> f = g
  := invmaponpathsweq (universalProperty _ _) _ _.

Definition universalMapUniqueness {C:Precategory} {X:[C,SET]} {r:Representation X}
      {c:C} (x : X ⇒ c) (f : universalObject r → c) :
  f ⟳ r = x -> f = x // r
  := pathsweq1 (universalProperty r c) f x.

Definition universalMapIdentity {C:Precategory} {X:[C,SET]} (r:Representation X) :
  r // r = identity _.
Proof. apply pathsinv0. apply universalMapUniqueness. apply arrow_mor_id. Qed.

Definition universalMapUniqueness' {C:Precategory} {X:[C,SET]} {r:Representation X}
      {c:C} (x : X ⇒ c) (f : universalObject r → c) :
  f = x // r -> f ⟳ r = x
  := pathsweq1' (universalProperty r c) f x.

Lemma universalMapNaturality {C:Precategory} {a:C} {Y Z:[C,SET]^op}
      (s : Representation Y)
      (t : Representation Z)
      (q : Z → Y) (f : universalObject s → a) :
  f ∘ (s ⟲ q // t) = f ⟳ s ⟲ q // t.
Proof.
  (* This lemma says that if the source and target of a natural transformation
  q are represented by objects of C, then q is represented by composition with
  an arrow of C. *)
  apply universalMapUniqueness.
  rewrite arrow_mor_mor_assoc.
  rewrite universalMapProperty.
  now rewrite nattrans_arrow_mor_assoc.
Qed.

(*  *)

Lemma B {C:Precategory} {X:[C,SET]^op} (r:Representation X) :
    r ⟲ identity X // r = identity _.
Proof.
  unfold nat_trans_id; simpl.
  rewrite identityFunction'. apply universalMapIdentity.
Qed.

Lemma B' {C:Precategory} {X Y Z:[C,SET]^op}
      (r:Representation X)
      (s:Representation Y)
      (t:Representation Z)
      (p:X→Y) (q:Y→Z) :
    t ⟲ (q ∘ p) // r = (t ⟲ q // s) ∘ (s ⟲ p // r).
Proof.
  rewrite <- nattrans_nattrans_arrow_assoc.
  rewrite universalMapNaturality.
  rewrite universalMapProperty.
  reflexivity.
Qed.

Definition universalObjectFunctor (C:Precategory) : RepresentedFunctor C ==> C^op.
Proof.
  refine (makeFunctor _ _ _ _).
  - intro X. exact (universalObject (pr2 X)).
  - intros X Y p; simpl. exact (pr2 X ⟲ p // pr2 Y).
  - intros X; simpl. apply B.
  - intros X Y Z p q; simpl. apply B'.
Defined.

Definition embeddingRepresentability {C D:Precategory}
           {i:C==>D} (emb:fully_faithful i) {Y:D==>SET} (s:Representation Y) :
           (Σ c, universalObject s = i c) -> Representation (Y □ i).
Proof.
  intros ce. exists (pr1 ce).
  exists (transportf (λ d, Y d : hSet) (pr2 ce) s).
  intro c'. apply (twooutof3c (# i) (λ g, g ⟳ _)).
  - apply emb.
  - induction (pr2 ce). exact (weqproperty (universalProperty _ _)).
Defined.

(*  *)
