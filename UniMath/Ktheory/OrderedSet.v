(* -*- coding: utf-8 -*- *)

(** * Ordered sets *)

(** see Bourbaki, Set Theory, III.1, where they are called totally ordered sets *)

Require Import UniMath.Foundations.FiniteSets
               UniMath.Ktheory.Utilities.

Unset Automatic Introduction.

Definition Oset := total2 (fun X : Poset => istotal (pr1 (pr2 X)) × isantisymm (pr1 (pr2 X))).

Definition underlyingSet (X:Oset) : hSet := pr1 X.
Coercion underlyingSet : Oset >-> hSet.

Definition underlyingRelation (X:Oset) := pr1 (pr2 (pr1 X)).

Notation "m ≤ n" := (underlyingRelation _ m n) (no associativity, at level 70) : oset_scope.
Open Scope oset_scope.
Notation "m ≥ n" := (n ≤ m) (no associativity, at level 70) : oset_scope.
Notation "m < n" := (m ≤ n × m != n) : oset_scope.
Notation "m > n" := (n < m) : oset_scope.

Definition stnoset (n:nat) : Oset.
Proof.
  intros.
  exists (stnposet n).
  split.
  { intros x y. apply istotalnatleh. }
  { intros ? ? ? ?.
    apply (an_inclusion_is_injective _ (isinclstntonat _)).
    { apply isantisymmnatleh. assumption. assumption. }}
Defined.

Definition isordered {X Y:Oset} (f:X->Y) := forall (x x':X), x ≤ x' -> f x ≤ f x'.

Lemma isapropisordered {X Y:Oset} (f:X->Y) : isaprop (isordered f).
Proof.
  intros; apply impredtwice; intros ; apply impred; intros _.
  apply isaprop_hProp.
Defined.

Definition Map (X Y:Oset) := total2 (fun f:X->Y => isordered f).

Definition FiniteStructure (X:Oset) := total2 (fun n => total2 (fun f : weq (stnoset n) X => isordered (pr1 f))).

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
      { apply isapropisweq. } }
    { intros; apply impredtwice; intros; apply impred; intros. apply pr2. }
  }
Abort.
