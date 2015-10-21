(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

Lemma poEquality {X:hSet} (R S:po X) :
  @isPosetEquivalence (X,,R) (X,,S) (idweq X) -> R=S.
Proof.
  intros ? ? ? e. apply total2_paths_second_isaprop. { apply isaprop_ispo. }
  induction R as [R r]; induction S as [S s]; simpl.
  apply funextfun; intro x; apply funextfun; intro y.
  unfold isPosetEquivalence in e.
  unfold isaposetmorphism in e; simpl in e.
  induction e as [e e']. apply uahp. { apply e. } { apply e'. }
Defined.

Definition isPosetEquivalence_idweq (X:Poset) : isPosetEquivalence (idweq X).
Proof.
  intros. split. { intros x y le. exact le. } { intros x y le. exact le. }  
Defined.

Lemma poTransport {X Y:hSet} (R:po X) (S:po Y) (f:X=Y) :
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f)
  -> transportf (po∘pr1hSet) f R = S.
Proof.
  intros ? ? ? ? ? i. induction f. apply poEquality. apply i.
Defined.

Lemma poTransport' {X Y:hSet} (R:po X) (S:po Y) (f:X=Y) :
  transportf (po∘pr1hSet) f R = S
  ->
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f).
Proof.
  intros ? ? ? ? ? e. induction f. induction e. apply isPosetEquivalence_idweq.
Defined.

Definition identityPosetEquivalence (X:Poset) : PosetEquivalence X X.
Proof. intros. exists (idweq X). apply isPosetEquivalence_idweq.
Defined.

Definition Poset_univalence_map {X Y:Poset} : X=Y -> PosetEquivalence X Y.
Proof. intros ? ? e. induction e. apply identityPosetEquivalence.
Defined.

Local Lemma Poset_univalence_prelim (X Y:Poset) : X=Y ≃ PosetEquivalence X Y.
Proof.
  Set Printing Coercions.
  intros. refine (weqcomp (total2_paths_equiv _ X Y) _).
  refine (weqbandf _ _ _ _).
  { apply hSet_univalence_weq. }
  intros e. apply eqweqmap. apply uahp'.
  { apply isaset_po. } { apply isaprop_isPosetEquivalence. }
  { apply poTransport'. } { apply poTransport. }
  Unset Printing Coercions.
Defined.

Local Definition Poset_univalence_compute {X Y:Poset} (f:X=Y) :
  Poset_univalence_prelim X Y f = Poset_univalence_map f.
Proof.
  intros. apply isinj_pr1_PosetEquivalence. induction f. reflexivity.
Defined.

Theorem Poset_univalence {X Y:Poset} : isweq (@Poset_univalence_map X Y).
Proof.
  intros.
  apply (isweqhomot (Poset_univalence_prelim X Y)).
  { intros f. apply Poset_univalence_compute. }
  apply weqproperty.
Defined.

Local Open Scope poset.

Corollary Poset_univalence_weq {X Y:Poset} : (X=Y) ≃ (X≅Y).
Proof. intros. exact (weqpair _ Poset_univalence).
Defined.

Corollary Poset_univalence_invmap {X Y:Poset} : X≅Y -> X=Y.
Proof. intros ? ? f. exact (invmap Poset_univalence_weq f).
Defined.

Corollary Poset_univalence_invmap_compute {X Y:Poset} (f:X≅Y) :
  f = Poset_univalence_map (Poset_univalence_invmap f).
Proof.
  intros. apply pathsinv0. exact (homotweqinvweq (@Poset_univalence_weq X Y) f).
Defined.

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
(* compare with transportD *)
Proof.  
  intros ? ? ? ? ? ? c. induction e. exact c.
Defined.

Definition posetTransportStructure  (C : ∀ (T:Poset) (t:T), UU)
  {X Y : Poset} (f : X ≅ Y) (x : X) (c : C X x) : C Y (f x).
Proof.  
  intros.
  assert (s := posetTransport (Poset_univalence_invmap f) c).
  rewrite <- (Poset_univalence_invmap_compute f) in s.
  exact s.
Defined.

Definition posetTransportRelation  (C : ∀ (T:Poset) (t u:T), UU)
  {X Y : Poset} (f : X ≅ Y) (x y : X) (c : C X x y) : C Y (f x) (f y).
Proof.  
  intros.
  assert (s := posetTransport2 (Poset_univalence_invmap f) c).
  rewrite <- (Poset_univalence_invmap_compute f) in s.
  exact s.
Defined.

(* applications: *)

Notation "m < n" := (m ≤ n × m != n)%poset (only parsing) :poset_scope.
Definition isMinimal {X:Poset} (x:X) := ∀ y, x≤y.
Definition isMaximal {X:Poset} (x:X) := ∀ y, y≤x.
Definition consecutive {X:Poset} (x y:X) := x<y × ∀ z, ¬ (x<z × z<y).

Lemma isaprop_isMinimal {X:Poset} (x:X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred; intros z. apply propproperty.
Defined.

Lemma isaprop_isMaximal {X:Poset} (x:X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred; intros z. apply propproperty.
Defined.

Lemma isaprop_consecutive {X:Poset} (x y:X) : isaprop (consecutive x y).
Proof.
  intros. unfold consecutive. apply isapropdirprod.
  { apply isapropdirprod. { apply pr2. } simpl. apply isapropneg. }
  apply impred; intro z. apply isapropneg.
Defined.

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
Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 80, no associativity) : oset_scope.
Notation "m ≤ n" := (underlyingRelation _ m n) (no associativity, at level 70) : oset_scope.
Notation "m < n" := (m ≤ n × m != n)%oset (only parsing) :oset_scope.
Close Scope poset.
Local Open Scope oset.

Definition paths_to_OrderedSetEquivalence {X Y:OrderedSet} : X=Y -> X≅Y.
Proof.
  intros ? ? e.
  Set Printing Coercions.
  apply Poset_univalence_map.
  apply maponpaths.
  exact e.
  Unset Printing Coercions.
Defined.

Theorem OrderedSet_univalence {X Y:OrderedSet} :
    isweq (@paths_to_OrderedSetEquivalence X Y).
Proof.
  intros.
  unfold paths_to_OrderedSetEquivalence.
  apply (twooutof3c (@maponpaths _ _ underlyingPoset X Y) Poset_univalence_map).
  { apply weq_on_paths_underlyingPoset. }
  apply Poset_univalence.
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
