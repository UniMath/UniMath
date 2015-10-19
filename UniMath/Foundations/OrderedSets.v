(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.

(** preliminaries on posets, move upstream *)

Definition PosetEquivalence (X Y:Poset) := Σ f:X≃Y, isaposetmorphism f.

Definition identityPosetEquivalence (X:Poset) : PosetEquivalence X X.
Proof. intros. exists (idweq X). intros x y le. exact le.
Defined.

Definition paths_to_poset_equivalences {X Y:Poset} : X=Y -> PosetEquivalence X Y.
Proof. intros ? ? e. induction e. apply identityPosetEquivalence.
Defined.

Theorem Poset_univalence {X Y:Poset} :
    isweq (@paths_to_poset_equivalences X Y).
Proof.
  intros.
  set (f := total2_paths_equiv _ X Y).


Abort.  



(** * Ordered sets *)

(** see Bourbaki, Set Theory, III.1, where they are called totally ordered sets *)


Definition isOrdered (X:Poset) := istotal (pr1 (pr2 X)) × isantisymm (pr1 (pr2 X)).

Definition OrderedSet := Σ X:Poset, isOrdered X.

Local Definition underlyingSet (X:OrderedSet) : hSet := pr1 X.
Coercion underlyingSet : OrderedSet >-> hSet.

Local Definition underlyingRelation (X:OrderedSet) := pr1 (pr2 (pr1 X)).

Delimit Scope oset_scope with oset. 
Notation "m ≤ n" := (underlyingRelation _ m n) (no associativity, at level 70) : oset_scope.
Notation "m < n" := (m ≤ n × m != n)%oset (only parsing) :oset_scope.
Open Scope oset_scope.

Definition isOrderedMap {X Y:OrderedSet} (f:X->Y) := ∀ x x', x ≤ x' -> f x ≤ f x'.

Local Lemma idfun_ordered {X:OrderedSet} : isOrderedMap (idfun X).
Proof. intros ? x y le. exact le. Defined.

Lemma isaprop_isOrderedMap {X Y:OrderedSet} (f:X->Y) : isaprop (isOrderedMap f).
Proof.
  intros. apply impredtwice; intros. apply impred; intros _. apply propproperty.
Defined.

Definition OrderedMap (X Y:OrderedSet) := Σ f:X->Y, isOrderedMap f.

Definition identityOrderedMap (X:OrderedSet) : OrderedMap X X.
Proof. intros. exists (idfun X). apply idfun_ordered. Defined.

Definition OrderedEquivalence (X Y:OrderedSet) := Σ f:X≃Y, isOrderedMap f.

Notation "X ≅ Y" := (OrderedEquivalence X Y) (at level 80, no associativity) : oset_scope.
(* written \cong in Agda input method *) 

Definition underlyingEquivalence {X Y} : X≅Y -> X≃Y := pr1.
Coercion underlyingEquivalence : OrderedEquivalence >-> weq.

Definition identityOrderedEquivalence (X:OrderedSet) : X ≅ X.
Proof. intros. exists (idweq X). apply idfun_ordered. Defined.

Definition paths_to_equivalences {X Y:OrderedSet} : X=Y -> X≅Y.
Proof.
  intros ? ? e.
  induction e.
  apply identityOrderedEquivalence.
Defined.

Theorem OrderedSet_univalence {X Y:OrderedSet} :
    isweq (@paths_to_equivalences X Y).
Proof.
  intros.
  set (f := total2_paths_equiv _ X Y).
  set (g := total2_paths_equiv _ (pr1 X) (pr1 Y)).

Abort.

Definition isMinimal {X:OrderedSet} (x:X) := ∀ y, x≤y.
Definition isMaximal {X:OrderedSet} (x:X) := ∀ y, y≤x.
Definition consecutive {X:OrderedSet} (x y:X) := x<y × ∀ z, ¬ (x<z × z<y).

Lemma isaprop_isMinimal {X:OrderedSet} (x:X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred; intros z. apply propproperty.
Defined.

Lemma isaprop_isMaximal {X:OrderedSet} (x:X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred; intros z. apply propproperty.
Defined.

Lemma isaprop_consecutive {X:OrderedSet} (x y:X) : isaprop (consecutive x y).
Proof.
  intros. unfold consecutive. apply isapropdirprod.
  { apply isapropdirprod. { apply pr2. } simpl. apply isapropneg. }
  apply impred; intro z. apply isapropneg.
Defined.

Lemma isMinimal_preserved {X Y:OrderedSet} {x:X} (is:isMinimal x) (f:X ≅ Y) : isMinimal (f x).
Proof.
  intros.


Abort.
  
(* standard ordered sets *)

Definition standardOrderedSet (n:nat) : OrderedSet.
Proof.
  intros. exists (stnposet n). split.
  { intros x y. apply istotalnatleh. }
  intros ? ? ? ?. apply isinjstntonat. now apply isantisymmnatleh.
Defined.

Local Notation "⟦ n ⟧" := (standardOrderedSet n) (at level 0). (* in agda-mode \[[ n \]] *)

Definition FiniteStructure (X:OrderedSet) := Σ n, Σ f:standardOrderedSet n ≃ X, isOrderedMap f.

Local Lemma std_auto n : iscontr (OrderedEquivalence ⟦ n ⟧ ⟦ n ⟧).
Proof.
  intros. exists (identityOrderedEquivalence _). intros f.
  apply total2_paths_isaprop.
  { intros g. apply isaprop_isOrderedMap. }
  simpl. apply isinjpr1weq. simpl. apply funextfun. intros i.
  induction i as [i l]; induction f as [f is]. induction i as [|i h].
  { simpl. 
    

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
    intros; apply impredtwice; intros; apply impred; intros. apply pr2.
  }
Abort.
