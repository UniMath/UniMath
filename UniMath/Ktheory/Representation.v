Require Import UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.Bifunctor.
Set Automatic Introduction.
Local Open Scope cat.

Definition Universal {C:Precategory} (X:[C^op,SET]) (c:C)
  := Σ (x:c ⇒ X), ∀ (c':C), isweq (λ f : c' → c, x ⟲ f).

Definition Representation {C:Precategory} (X:[C^op,SET]) : UU
  := Σ (c:C), Universal X c.

Definition isRepresentable {C:Precategory} (X:[C^op,SET]) := ∥ Representation X ∥.

Lemma isaprop_Representation {C:category} (X:[C^op,SET]) :
  isaprop (@Representation C X).
Proof.

Abort.

(* categories of functors with representations *)

Definition RepresentedFunctor (C:Precategory) : Precategory
  := @categoryWithStructure [C^op,SET] Representation.

Definition toRepresentation {C:Precategory} (X : RepresentedFunctor C) :
  Representation (pr1 X)
  := pr2 X.

Definition RepresentableFunctor (C:Precategory) : Precategory
  := @categoryWithStructure [C^op,SET] isRepresentable.

Definition toRepresentableFunctor {C:Precategory} :
  RepresentedFunctor C ==> RepresentableFunctor C :=
  functorWithStructures (λ c, hinhpr).

(* make a representation of a functor *)

Definition makeRepresentation {C:Precategory} {c:C} {X:[C^op,SET]} (x:c ⇒ X) :
  (∀ (c':C), bijective (λ f : c' → c, x ⟲ f)) -> Representation X.
Proof.
  intros bij. exists c. exists x. intros c'. apply set_bijection_to_weq.
  - exact (bij c').
  - apply setproperty.
Defined.

(* universal aspects of represented functors *)

Definition universalObject {C:Precategory} {X:[C^op,SET]} (r:Representation X) : C
  := pr1 r.

Definition universalElement {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  universalObject r ⇒ X
  := pr1 (pr2 r).

Coercion universalElement : Representation >-> pr1hSet.

Definition universalProperty {C:Precategory} {X:[C^op,SET]} (r:Representation X) (c:C) :
  c → universalObject r ≃ c ⇒ X
  := weqpair (λ f : c → universalObject r, r ⟲ f)
             (pr2 (pr2 r) c).

Definition universalMap {C:Precategory} {X:[C^op,SET]} (r:Representation X) {c:C} :
  c ⇒ X -> c → universalObject r
  := invmap (universalProperty _ _).

Notation "r \\ x" := (universalMap r x) (at level 50, left associativity) : cat.

Definition universalMapProperty {C:Precategory} {X:[C^op,SET]} {r:Representation X}
      {c:C} (x : c ⇒ X) :
  r ⟲ (r \\ x) = x
  := homotweqinvweq (universalProperty r c) x.

Definition mapUniqueness {C:Precategory} (X:[C^op,SET]) (r : Representation X) (c:C)
           (f g: c → universalObject r) :
  r ⟲ f = r ⟲ g -> f = g
  := invmaponpathsweq (universalProperty _ _) _ _.

Definition universalMapUniqueness {C:Precategory} {X:[C^op,SET]} {r:Representation X}
      {c:C} (x : c ⇒ X) (f : c → universalObject r) :
  r ⟲ f = x -> f = r \\ x
  := pathsweq1 (universalProperty r c) f x.

Definition universalMapIdentity {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  r \\ r = identity _.
Proof. apply pathsinv0. apply universalMapUniqueness. apply arrow_mor_id. Qed.

Definition universalMapUniqueness' {C:Precategory} {X:[C^op,SET]} {r:Representation X}
      {c:C} (x : c ⇒ X) (f : c → universalObject r) :
  f = r \\ x -> r ⟲ f = x
  := pathsweq1' (universalProperty r c) f x.

Lemma universalMapNaturality {C:Precategory} {a:C} {Y Z:[C^op,SET]}
      (s : Representation Y)
      (t : Representation Z)
      (q : Y → Z) (f : a → universalObject s) :
  (t \\ (q ⟳ s)) ∘ f = t \\ (q ⟳ s ⟲ f).
Proof.
  (* This lemma says that if the source and target of a natural transformation
  q are represented by objects of C, then q is represented by composition with
  an arrow of C. *)
  apply universalMapUniqueness.
  rewrite arrow_mor_mor_assoc.
  rewrite universalMapProperty.
  now rewrite <- nattrans_arrow_mor_assoc.
Qed.

(*  *)

Lemma B {C:Precategory} {X:[C^op,SET]} (r:Representation X) :
  r \\ (identity X ⟳ r) = identity _.
Proof.
  unfold nat_trans_id; simpl.
  rewrite identityFunction'. apply universalMapIdentity.
Qed.

Lemma B' {C:Precategory} {X Y Z:[C^op,SET]}
      (r:Representation X)
      (s:Representation Y)
      (t:Representation Z)
      (p:X→Y) (q:Y→Z) :
    t \\ ((q ∘ p) ⟳ r) = (t \\ (q ⟳ s)) ∘ (s \\ (p ⟳ r)).
Proof.
  rewrite <- nattrans_nattrans_arrow_assoc.
  rewrite universalMapNaturality.
  rewrite <- nattrans_arrow_mor_assoc.
  rewrite universalMapProperty.
  reflexivity.
Qed.

Definition universalObjectFunctor (C:Precategory) : RepresentedFunctor C ==> C.
Proof.
  refine (makeFunctor _ _ _ _).
  - intro X. exact (universalObject (pr2 X)).
  - intros X Y p; simpl. exact (pr2 Y \\ (p ⟳ pr2 X)).
  - intros X; simpl. apply B.
  - intros X Y Z p q; simpl. apply B'.
Defined.

Definition embeddingRepresentability {C D:Precategory}
           {i:C==>D} (emb:fully_faithful i) {Y:D^op==>SET} (s:Representation Y) :
           (Σ c, universalObject s = i c) -> Representation (Y □ functor_opp i).
Proof.
  intros ce. exists (pr1 ce).
  exists (transportf (λ d, Y d : hSet) (pr2 ce) s).
  intro c'. apply (twooutof3c (# i) (λ g, _ ⟲ g)).
  - apply emb.
  - induction (pr2 ce). exact (weqproperty (universalProperty _ _)).
Defined.

(*** Some standard functors to consider representing *)

(** products and coproducts *)

Definition HomFamily (C:Precategory) {I} (c:I -> ob C) : C^op ==> SET.
Proof.
  intros.
  refine (_,,_).
  - refine (_,,_).
    + intros x. exact (∀ i, Hom C x (c i)) % set.
    + intros x y f p i; simpl; simpl in p.
      exact (p i ∘ (f : Hom C y x)).
  - split.
    + intros a. apply funextsec; intros f; apply funextsec; intros i; simpl.
      apply id_left.
    + intros x y z p q.
      apply funextsec; intros f; apply funextsec; intros i; simpl.
      apply pathsinv0, assoc.
Defined.

Definition Product {C:Precategory} {I} (c:I -> ob C)
  := Representation (HomFamily C c).

Definition Sum {C:Precategory} {I} (c:I -> ob C)
  := Representation (HomFamily C^op c).

Local Open Scope cat'.

Require Import UniMath.Ktheory.ZeroObject.

Definition Annihilator (C:Precategory) (z:hasZeroObject C) {c d:ob C} (f:c → d) :
  C^op ==> SET.
Proof.
  refine (_,,_).
  { refine (_,,_).
    { intro b. exists (Σ g:Hom C b c, f ∘ g = @zeroMap C z b d).
      abstract (apply isaset_total2; [ apply setproperty |
      intro g; apply isasetaprop; apply homset_property ]) using L. }
    { intros a b p ge; simpl.
      exists (pr1 ge ∘ opp_mor p).
      { abstract (
            refine (! assoc _ _ _ @ _); rewrite (pr2 ge);
            apply zeroMap_right_composition) using M. } } }
  { abstract (split;
    [ intros x; apply funextsec; intros [r rf0];
      apply subtypeEquality;
      [ intro; apply homset_property
      | simpl; unfold opp_mor; apply id_left ]
    | intros w x y t u; apply funextsec; intros [r rf0];
      apply subtypeEquality;
      [ intro; apply homset_property
      | simpl; unfold opp_mor; apply pathsinv0, assoc ] ]) using N. }
Defined.

Definition Kernel {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
  Representation (Annihilator C z f).

Definition Cokernel {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
  Representation (Annihilator C^op (haszero_opp C z) f).

Definition kernelMap {C:Precategory} {z:hasZeroObject C} {c d:ob C} {f:c → d}
           (r : Kernel z f) : universalObject r → c
  := pr1 (universalElement r).

Definition kernelEquation {C:Precategory} {z:hasZeroObject C} {c d:ob C} {f:c → d}
           (ker : Kernel z f) :
  f ∘ kernelMap ker = zeroMap C z _ _
  := pr2 (universalElement ker).

Definition cokernelMap {C:Precategory} {z:hasZeroObject C} {c d:ob C} {f:c → d}
           (r : Cokernel z f) : d → universalObject r
  := pr1 (universalElement r).

Definition cokernelEquation {C:Precategory} {z:hasZeroObject C} {c d:ob C} {f:c → d}
           (coker : Cokernel z f) :
  cokernelMap coker ∘ f = zeroMap C z _ _.
  assert (L := pr2 (universalElement coker)). simpl in L.

Abort.

Module demo.

  Section A.

    Context {C:Precategory} (z:hasZeroObject C) {c d:ob C} (f:c → d)
            (ker: Kernel z f) (coker: Cokernel z f).

    Definition h := kernelMap ker.

    Definition b := src h.

    Definition e : f ∘ h = zeroMap C z b d
      := kernelEquation ker.

    Definition k := cokernelMap coker.

    Definition a := tar k.

    (* Definition e' : k ∘ f = zeroMap C z c a *)
    (*   := cokernelEquation ker. *)

  End A.

End demo.
