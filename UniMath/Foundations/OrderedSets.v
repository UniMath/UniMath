(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.
Local Open Scope poset.

(** partially ordered sets and ordered sets *)

Definition Poset_univalence_map {X Y:Poset} : X=Y -> PosetEquivalence X Y.
Proof. intros ? ? e. induction e. apply identityPosetEquivalence.
Defined.

Lemma posetStructureIdentity {X:hSet} (R S:po X) :
  @isPosetEquivalence (X,,R) (X,,S) (idweq X) -> R=S.
Proof.
  intros ? ? ? e. apply total2_paths_second_isaprop. { apply isaprop_ispo. }
  induction R as [R r]; induction S as [S s]; simpl.
  apply funextfun; intro x; apply funextfun; intro y.
  unfold isPosetEquivalence in e.
  unfold isaposetmorphism in e; simpl in e.
  induction e as [e e']. apply uahp. { apply e. } { apply e'. }
Defined.

Lemma poTransport_logeq {X Y:hSet} (R:po X) (S:po Y) (f:X=Y) :
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f)
  <-> transportf (po∘pr1hSet) f R = S.
Proof.
  split.
  { intros i. induction f. apply posetStructureIdentity. apply i. }
  { intros e. induction f. induction e. apply isPosetEquivalence_idweq. }
Defined.

Corollary poTransport_weq {X Y:hSet} (R:po X) (S:po Y) (f:X=Y) :
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f)
  ≃ transportf (po∘pr1hSet) f R = S.
Proof.
  intros.
  apply eqweqmap. apply uahp'.
  { apply isaprop_isPosetEquivalence. } { apply isaset_po. }
  { apply (pr1 (poTransport_logeq _ _ _)). } { apply (pr2 (poTransport_logeq _ _ _)). }
Defined.

Local Lemma posetTransport_weq (X Y:Poset) : X≡Y ≃ X≅Y.
Proof.
  intros.
  refine (weqbandf _ _ _ _).
  { apply hSet_univalence_weq. }
  intros e. apply invweq. apply poTransport_weq.
Defined.

Theorem Poset_univalence (X Y:Poset) : X=Y ≃ X≅Y.
Proof.
  intros.
  set (f := @Poset_univalence_map X Y).
  set (g := total2_paths_equiv _ X Y).
  set (h := posetTransport_weq X Y).
  set (f' := weqcomp g h).
  assert (k : pr1weq f' ~ f).
  { intro e. apply isinj_pr1_PosetEquivalence. induction e. reflexivity. }
  assert (l : isweq f).
  { apply (isweqhomot f'). exact k. apply weqproperty. }
  exact (f,,l).
Defined.

Definition Poset_univalence_compute {X Y:Poset} (f:X=Y) :
  Poset_univalence X Y f = Poset_univalence_map f.
Proof. reflexivity. Defined.

(* now we try to mimic this construction:

    Inductive PosetEquivalence (X Y:Poset) : Type := pathToEq : (X=Y) -> PosetEquivalence X Y.

    PosetEquivalence_rect
         : ∀ (X Y : Poset) (P : PosetEquivalence X Y -> Type),
           (∀ e : X = Y, P (pathToEq X Y e)) ->
           ∀ p : PosetEquivalence X Y, P p

*)

Theorem PosetEquivalence_rect
         : ∀ (X Y : Poset) (P : PosetEquivalence X Y -> Type),
           (∀ e : X = Y, P (Poset_univalence_map e)) ->
           ∀ f : PosetEquivalence X Y, P f.
Proof.
  intros ? ? ? ih ?.
Admitted.

Lemma B {X Y:Poset} (x:X) (e : X = Y) :
      transportf (λ T : Poset, T) e x = (Poset_univalence_map e) x.
Proof. intros. induction e. reflexivity.
Defined.

Definition posetTransport {C : ∀ (T:Poset) (t:T), UU}
  {X Y : Poset} (e : X = Y) {x : X} : C X x -> C Y (Poset_univalence_map e x).
(* compare with transportD *)
Proof.  
  intros ? ? ? ? ? c. induction e. exact c.
Defined.

Definition posetTransport2 {C : ∀ (T:Poset) (t u:T), UU}
  {X Y : Poset} (e : X = Y) {x y : X} : C X x y -> C Y (Poset_univalence_map e x) (Poset_univalence_map e y).
Proof.  
  intros ? ? ? ? ? ? c. induction e. exact c.
Defined.

Definition posetTransportStructure  (C : ∀ (T:Poset) (t:T), UU)
  {X Y : Poset} (f : X ≅ Y) (x : X) (c : C X x) : C Y (f x).
Proof.  
  intros.
  assert (s := posetTransport (invmap (Poset_univalence _ _) f) c).
  assert (t := homotweqinvweq (Poset_univalence X Y) f).
  rewrite <- t.
  exact s.
Defined.

Definition posetTransportRelation  (C : ∀ (T:Poset) (t u:T), UU)
  {X Y : Poset} (f : X ≅ Y) (x y : X) (c : C X x y) : C Y (f x) (f y).
Proof.  
  intros.
  assert (s := posetTransport2 (invmap (Poset_univalence _ _) f) c).
  assert (t := homotweqinvweq (Poset_univalence X Y) f).
  rewrite <- t.
  exact s.
Defined.

(* applications: *)

Lemma isMinimal_preserved {X Y:Poset} {x:X} (is:isMinimal x) (f:X ≅ Y) : isMinimal (f x).
Proof.
  intros. apply posetTransportStructure. exact is.
Defined.

Lemma isMinimal_preserved' {X Y:Poset} {x:X} (is:isMinimal x) (f:X ≅ Y) : isMinimal (f x).
Proof.
  intros. generalize f; apply PosetEquivalence_rect; intro e; clear f.
  induction e. exact is.
Defined.

Lemma consecutive_preserved {X Y:Poset} {x y:X} (is:consecutive x y) (f:X ≅ Y) : consecutive (f x) (f y).
Proof.
  intros. apply posetTransportRelation. exact is.
Defined.

Lemma consecutive_preserved' {X Y:Poset} {x y:X} (is:consecutive x y) (f:X ≅ Y) : consecutive (f x) (f y).
Proof.
  intros.
  (* Anders says " induction f. " should look for PosetEquivalence_rect.  Why doesn't it? *)
  generalize f; apply PosetEquivalence_rect; intro e; clear f.
  induction e. exact is.
Defined.

(** * Ordered sets *)

(** see Bourbaki, Set Theory, III.1, where they are called totally ordered sets *)


Definition isOrdered (X:Poset) := istotal (pr1 (pr2 X)) × isantisymm (pr1 (pr2 X)).

Lemma isaprop_isOrdered (X:Poset) : isaprop (isOrdered X).
Proof.
  intros. apply isapropdirprod. { apply isaprop_istotal. } { apply isaprop_isantisymm. }
Defined.

Definition OrderedSet := Σ X, isOrdered X.

Local Definition underlyingPoset (X:OrderedSet) : Poset := pr1 X.
Coercion underlyingPoset : OrderedSet >-> Poset.

Local Definition underlyingRelation (X:OrderedSet) := pr1 (pr2 (pr1 X)).

Lemma isincl_underlyingPoset : isincl underlyingPoset.
Proof.
  apply isinclpr1. intros X. apply isaprop_isOrdered.
Defined.

Lemma isinj_underlyingPoset : isinj underlyingPoset.
Proof.
  apply invmaponpathsincl. apply isincl_underlyingPoset.
Defined.

Lemma weq_on_paths_underlyingPoset (X Y:OrderedSet) : isweq (@maponpaths _ _ underlyingPoset X Y).
Proof.
  intros. apply isweqonpathsincl. apply isincl_underlyingPoset.
Defined.

Delimit Scope oset_scope with oset. 
Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 60, no associativity) : oset_scope.
Notation "m ≤ n" := (underlyingRelation _ m n) (no associativity, at level 70) : oset_scope.
Notation "m < n" := (m ≤ n × m != n)%oset (only parsing) :oset_scope.
Close Scope poset.
Local Open Scope oset.

Definition OrderedSetEquivalence_map {X Y:OrderedSet} : X=Y -> X≅Y.
Proof.
  intros ? ? e.
  Set Printing Coercions.
  apply Poset_univalence_map.
  apply maponpaths.
  exact e.
  Unset Printing Coercions.
Defined.

Theorem OrderedSet_univalence {X Y:OrderedSet} : X=Y ≃ X≅Y.
Proof.
  (* shorten this *)
  intros.
  exists OrderedSetEquivalence_map.
  unfold OrderedSetEquivalence_map.
  apply (twooutof3c (@maponpaths _ _ underlyingPoset X Y) Poset_univalence_map).
  { apply weq_on_paths_underlyingPoset. }
  apply (pr2 (Poset_univalence _ _)).
Defined.
  
(* standard ordered sets *)

Definition standardOrderedSet (n:nat) : OrderedSet.
Proof.
  intros. exists (stnposet n). split.
  { intros x y. apply istotalnatleh. }
  intros ? ? ? ?. apply isinjstntonat. now apply isantisymmnatleh.
Defined.

Local Notation "⟦ n ⟧" := (standardOrderedSet n) (at level 0). (* in agda-mode \[[ n \]] *)

Definition FiniteStructure (X:OrderedSet) := Σ n, standardOrderedSet n ≅ X.

Local Lemma std_auto n : iscontr (⟦ n ⟧ ≅ ⟦ n ⟧).
Proof.
  intros. exists (identityPosetEquivalence _). intros f.
  apply total2_paths_isaprop.
  { intros g. apply isaprop_isPosetEquivalence. }
  simpl. apply isinjpr1weq. simpl. apply funextfun. intros i.
    

Abort.

Lemma isapropFiniteStructure X : isaprop (FiniteStructure X).
Proof.
  intros.
  apply invproofirrelevance; intros r s.
  destruct r as [m p].
  destruct s as [n q].
  apply total2_paths2_second_isaprop.
  { 
    apply weqtoeqstn.
    exact (weqcomp (pr1 p) (invweq (pr1 q))).
  }
  {
    intros k.
    apply invproofirrelevance; intros [[r b] i] [[s c] j]; simpl in r,s,i,j.
    apply total2_paths2_second_isaprop.
    { 
      apply total2_paths2_second_isaprop.
      { 
        
        
        
        admit. }
      apply isapropisweq. }
    apply isaprop_isPosetEquivalence.
  }
Abort.
