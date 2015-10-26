(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.
Require Import UniMath.Foundations.FunctionalExtensionality.
Local Open Scope poset.
Local Notation "● x" := (x,,idpath _) (at level 35).

(* propositions, move upstream *)

Lemma neg_isdecprop {X} : isdecprop X -> isdecprop (¬ X).
Proof.
  intros ? i.
  assert (j := isdecproptoisaprop X i).
  apply isdecpropif.
  { apply isapropneg. }
  unfold isdecprop in i.
  assert (k := pr1 i); clear i.
  induction k as [k|k].
  { apply ii2. now apply todneg. }
  now apply ii1.
Defined.

(* decidable propositions, move upstream *)

Definition DecidableProposition := Σ X:UU, isdecprop X.

Definition DecidableProposition_to_hProp : DecidableProposition -> hProp.
Proof.
  intros X.
  exact (pr1 X,, isdecproptoisaprop (pr1 X) (pr2 X)).
Defined.
Coercion DecidableProposition_to_hProp : DecidableProposition >-> hProp.
Definition decidabilityProperty (X:DecidableProposition) :
  isdecprop X := pr2 X.

Definition DecidableSubtype (X:UU) := X -> DecidableProposition.
Definition DecidableRelation (X:UU) := X -> X -> DecidableProposition.

Definition DecidableSubtype_to_hsubtypes {X} (P:DecidableSubtype X) : hsubtypes X
  := λ x, DecidableProposition_to_hProp(P x).
Coercion DecidableSubtype_to_hsubtypes : DecidableSubtype >-> hsubtypes.

Definition DecidableRelation_to_hsubtypes {X} (P:DecidableRelation X) : hrel X
  := λ x y, DecidableProposition_to_hProp(P x y).
Coercion DecidableRelation_to_hsubtypes : DecidableRelation >-> hrel.

Ltac choose P yes no := induction (iscontrpr1 (decidabilityProperty P)) as [yes|no].

Definition choice {W} : DecidableProposition -> W -> W -> W.
Proof.
  intros ? P yes no.
  choose P p q.
  - exact yes.
  - exact no.
Defined.

Definition choice_compute_yes {W} (P:DecidableProposition) (p:P) (yes no:W) :
  choice P yes no = yes.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. reflexivity.
  - simpl. contradicts p b.
Defined.  

Definition choice_compute_no {W} (P:DecidableProposition) (p:¬P) (yes no:W) :
  choice P yes no = no.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. contradicts p a.
  - simpl. reflexivity.
Defined.  

Definition underlyingType {X} : DecidableSubtype X -> UU.
Proof. intros ? S. exact (Σ x, S x). Defined.

Definition underlyingType' {X} : DecidableSubtype X -> UU.
Proof. intros ? P.
       (* for use with isfinitedecsubset *)
       exact (hfiber (λ x, choice (P x) true false) true).
Defined.

Definition underlyingType_weq {X} (P:DecidableSubtype X) :
  underlyingType' P ≃ underlyingType P.
Proof.
  intros.
  apply weqfibtototal.
  intros x.
  unfold choice.
  simpl.
  change (iscontrpr1 (decidabilityProperty (P x))) with (iscontrpr1 (decidabilityProperty (P x))).
  choose (P x) p q.
  - simpl. apply weqiff.
    + apply logeq_both_true.
      * reflexivity.
      * assumption.
    + apply isasetbool.    
    + apply (propproperty (DecidableProposition_to_hProp _)).
  - simpl. apply weqiff.
    + apply logeq_both_false.
      * now apply falsetonegtrue.
      * assumption.
    + apply isasetbool.    
    + apply (propproperty (DecidableProposition_to_hProp _)).
Defined.

Lemma subsetFiniteness {X} (P : DecidableSubtype X) :
  isfinite X -> isfinite (underlyingType P).
Proof.
  intros ? ? is.
  assert (fin : isfinite (underlyingType' P)).
  { now apply isfinitedecsubset. }
  refine (isfiniteweqf _ fin).
  apply underlyingType_weq.
Defined.

Coercion underlyingType : DecidableSubtype >-> UU.

Definition decrel_to_DecidableRelation {X} : decrel X -> DecidableRelation X.
Proof.
  intros ? R x y. induction R as [R is]. exists (R x y).
  apply isdecpropif. { apply propproperty. } apply is.
Defined.

Definition natlth_DecidableProposition := decrel_to_DecidableRelation natlthdec.
Definition natleh_DecidableProposition := decrel_to_DecidableRelation natlehdec.
Definition natgth_DecidableProposition := decrel_to_DecidableRelation natgthdec.
Definition natgeh_DecidableProposition := decrel_to_DecidableRelation natgehdec.
Definition nateq_DecidableProposition := decrel_to_DecidableRelation natdeceq.
Definition natneq_DecidableProposition := decrel_to_DecidableRelation natdecneq.

Notation " x <? y " := ( natlth_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x <=? y " := ( natleh_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x ≤? y " := ( natleh_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x >=? y " := ( natgeh_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x ≥? y " := ( natgeh_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x >? y " := ( natgth_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x =? y " := ( nateq_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.
Notation " x !=? y " := ( natneq_DecidableProposition x y ) (at level 70, no associativity) : nat_scope.

Local Definition bound01 (P:DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  intros.
  unfold choice.
  choose P p q.
  { simpl. now apply falsetonegtrue. }
  { simpl. now apply falsetonegtrue. }
Defined.  

Definition tallyStandardSubset {n} (P: DecidableSubtype (stn n)) : stn (S n).
Proof. intros. exists (stnsum (λ x, choice (P x) 1 0)). apply natlehtolthsn.
       apply istransnatleh with (m := stnsum(λ _ : stn n, 1)).
       { apply stnsum_le; intro i. apply bound01. }
       assert ( p : ∀ r s, r = s -> (r ≤ s)%nat). { intros ? ? e. destruct e. apply isreflnatleh. }
       apply p. apply stnsum_1.
Defined.
Goal 3 = tallyStandardSubset (λ i:stn 7, 2*i <? 6). Proof. reflexivity. Defined.
Goal 1 = tallyStandardSubset (λ i:stn 7, 2*i =? 6). Proof. reflexivity. Defined.
Goal 6 = tallyStandardSubset (λ i:stn 7, 2*i !=? 4). Proof. reflexivity. Defined.

Definition tallyStandardSubsetSegment {n} (P: DecidableSubtype (stn n))
           (i:stn n) : stn n.
(* count how many elements less than i satisfy P *)
Proof.
  intros.
  assert (k := tallyStandardSubset
                 (λ j:stn i, P (stnincl i n (natlthtoleh i n (pr2 i)) j))).
  apply (stnincl (S i) n).
  { apply natlthtolehsn. exact (pr2 i). }
  exact k.
Defined.
Goal 3 = tallyStandardSubsetSegment (λ i:stn 14, 2*i <? 6) (●7). Proof. reflexivity. Defined.
Goal 6 = tallyStandardSubsetSegment (λ i:stn 14, 2*i !=? 4) (●7). Proof. reflexivity. Defined.

(* types and univalence *)

Theorem UU_rect (X Y : UU) (P : X ≃ Y -> UU) :
  (∀ e : X=Y, P (univalence _ _ e)) -> ∀ f, P f.
Proof.
  intros ? ? ? ih ?.
  set (p := ih (invmap (univalence _ _) f)).
  set (h := homotweqinvweq (univalence _ _) f).
  exact (transportf P h p).
Defined.

Ltac type_induction f e := generalize f; apply UU_rect; intro e; clear f.

Definition weqbandf' { X Y : UU } (w : X ≃ Y )
           (P:X -> UU) (Q: Y -> UU)
           ( fw : ∀ x:X, P x ≃ Q (w x) ) :
  (Σ x, P x) ≃ (Σ y, Q y).
Proof.
  intros.
  generalize w.
  apply UU_rect; intro e.
  (* this is a case where applying UU_rect is not as good as induction would be... *)
Abort.

Theorem hSet_rect (X Y : hSet) (P : X ≃ Y -> UU) :
  (∀ e : X=Y, P (hSet_univalence _ _ e)) -> ∀ f, P f.
Proof.
  intros ? ? ? ih ?.
  Set Printing Coercions.
  set (p := ih (invmap (hSet_univalence _ _) f)).
  set (h := homotweqinvweq (hSet_univalence _ _) f).
  exact (transportf P h p).
  Unset Printing Coercions.
Defined.

Ltac hSet_induction f e := generalize f; apply UU_rect; intro e; clear f.

(** partially ordered sets and ordered sets *)

Definition Poset_univalence_map {X Y:Poset} : X=Y -> PosetEquivalence X Y.
Proof. intros ? ? e. induction e. apply identityPosetEquivalence.
Defined.

Local Arguments isPosetEquivalence : clear implicits.
Local Arguments isaposetmorphism : clear implicits.

Lemma posetStructureIdentity {X:hSet} (R S:po X) :
  @isPosetEquivalence (X,,R) (X,,S) (idweq X) -> R=S.
Proof.
  intros ? ? ? e.
  apply total2_paths_second_isaprop. { apply isaprop_ispo. }
  induction R as [R r]; induction S as [S s]; simpl.
  apply funextfun; intro x; apply funextfun; intro y.
  unfold isPosetEquivalence in e.
  unfold isaposetmorphism in e; simpl in e.
  induction e as [e e'].
  unfold posetRelation in *. unfold invmap in *; simpl in *.
  apply uahp. { apply e. } { apply e'. }
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
  intros. apply weqimplimpl.
  { apply (pr1 (poTransport_logeq _ _ _)). }
  { apply (pr2 (poTransport_logeq _ _ _)). }
  { apply isaprop_isPosetEquivalence. }
  { apply isaset_po. }
Defined.

Local Lemma posetTransport_weq (X Y:Poset) : X≡Y ≃ X≅Y.
Proof.
  intros.
  refine (weqbandf _ _ _ _).
  { apply hSet_univalence. }
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
  try reflexivity.              (* this doesn't work *)
  { intro e. apply isinj_pr1_PosetEquivalence. induction e. reflexivity. }
  assert (l : isweq f).
  { apply (isweqhomot f'). exact k. apply weqproperty. }
  exact (f,,l).
Defined.

Definition Poset_univalence_compute {X Y:Poset} (e:X=Y) :
  Poset_univalence X Y e = Poset_univalence_map e.
Proof. reflexivity. Defined.

(* now we try to mimic this construction:

    Inductive PosetEquivalence (X Y:Poset) : Type := 
                  pathToEq : (X=Y) -> PosetEquivalence X Y.

    PosetEquivalence_rect
         : ∀ (X Y : Poset) (P : PosetEquivalence X Y -> Type),
           (∀ e : X = Y, P (pathToEq X Y e)) ->
           ∀ p : PosetEquivalence X Y, P p

*)

Theorem PosetEquivalence_rect (X Y : Poset) (P : X ≅ Y -> UU) :
  (∀ e : X = Y, P (Poset_univalence_map e)) -> ∀ f, P f.
Proof.
  intros ? ? ? ih ?.
  set (p := ih (invmap (Poset_univalence _ _) f)).
  set (h := homotweqinvweq (Poset_univalence _ _) f).
  exact (transportf P h p).
Defined.

Ltac poset_induction f e :=
  generalize f; apply PosetEquivalence_rect; intro e; clear f.

(* applications of poset equivalence induction: *)

Lemma isMinimal_preserved {X Y:Poset} {x:X} (is:isMinimal x) (f:X ≅ Y) :
  isMinimal (f x).
Proof.
  intros.
  (* Anders says " induction f. " should look for PosetEquivalence_rect.  
     Why doesn't it? *)
  poset_induction f e. induction e. simpl. exact is.
Defined.

Lemma isMaximal_preserved {X Y:Poset} {x:X} (is:isMaximal x) (f:X ≅ Y) :
  isMaximal (f x).
Proof. intros. poset_induction f e. induction e. simpl. exact is.
Defined.

Lemma consecutive_preserved {X Y:Poset} {x y:X} (is:consecutive x y) (f:X ≅ Y) : consecutive (f x) (f y).
Proof. intros. poset_induction f e. induction e. simpl. exact is.
Defined.

(** * Ordered sets *)

(** see Bourbaki, Set Theory, III.1, where they are called totally ordered sets *)


Definition isOrdered (X:Poset) := istotal (posetRelation X) × isantisymm (posetRelation X).

Lemma isaprop_isOrdered (X:Poset) : isaprop (isOrdered X).
Proof.
  intros. apply isapropdirprod. { apply isaprop_istotal. } { apply isaprop_isantisymm. }
Defined.

Definition OrderedSet := Σ X, isOrdered X.

Local Definition underlyingPoset (X:OrderedSet) : Poset := pr1 X.
Coercion underlyingPoset : OrderedSet >-> Poset.

Delimit Scope oset with oset. 

Definition Poset_lessthan {X:Poset} (x y:X) := (x ≤ y) ∧ (hneg (x = y)).

Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 60, no associativity) : oset.
Notation "m ≤ n" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "m < n" := (Poset_lessthan m n) :oset.

Close Scope poset.
Local Open Scope oset.

Definition OrderedSet_isrefl {X:OrderedSet} (x:X) :
  x ≤ x :=
  pr2 (pr2 (pr2 (pr1 X))) x.

Definition OrderedSet_isantisymm {X:OrderedSet} (x y:X) :
  x ≤ y -> y ≤ x -> x = y :=
  pr2 (pr2 X) x y.

Definition OrderedSet_istotal {X:OrderedSet} (x y:X) :
  x ≤ y ∨ y ≤ x :=
  pr1 (pr2 X) x y.
  
Lemma isdeceq_isdec_ordering (X:OrderedSet) : isdeceq X -> isdec_ordering X.
Proof.
  intros ? deceq ? ?.
  apply (OrderedSet_istotal x y); intro s. induction s as [s|s].
  { now apply ii1. }
  induction (deceq x y) as [j|j].
  { apply ii1. rewrite <- j. apply OrderedSet_isrefl. }
  apply ii2. intro le. apply j. now apply OrderedSet_isantisymm.
Defined.

Corollary isfinite_isdec_ordering (X:OrderedSet) : isfinite X -> isdec_ordering X.
Proof. intros ? i ? ?. apply isdeceq_isdec_ordering. now apply isfinite_isdeceq.
Defined.

Corollary isdeceq_isdec_lessthan (X:OrderedSet) :
  isdeceq X -> ∀ (x y:X), decidable (x < y).
Proof.
  intros ? i ? ?. apply decidable_dirprod.
  - now apply isdeceq_isdec_ordering.
  - apply neg_isdecprop.
    apply isdecpropif.
    * apply setproperty.
    * apply i.
Defined.

Corollary isfinite_isdec_lessthan (X:OrderedSet) : isfinite X -> ∀ (x y:X), decidable (x < y).
Proof. intros ? i ? ?. apply isdeceq_isdec_lessthan. now apply isfinite_isdeceq.
Defined.

Lemma isincl_underlyingPoset : isincl underlyingPoset.
Proof.
  apply isinclpr1. intros X. apply isaprop_isOrdered.
Defined.

Definition underlyingPoset_weq (X Y:OrderedSet) :
  X=Y ≃ (underlyingPoset X)=(underlyingPoset Y).
Proof.
  Set Printing Coercions.
  intros. refine (weqpair _ _).
  { apply maponpaths. }
  apply isweqonpathsincl. apply isincl_underlyingPoset.
  Unset Printing Coercions.
Defined.

Theorem OrderedSet_univalence (X Y:OrderedSet) : X=Y ≃ X≅Y.
Proof. intros. exact ((Poset_univalence _ _) ∘ (underlyingPoset_weq _ _))%weq.
Defined.

Theorem OrderedSetEquivalence_rect (X Y : OrderedSet) (P : X ≅ Y -> UU) :
  (∀ e : X = Y, P (OrderedSet_univalence _ _ e)) -> ∀ f, P f.
Proof.
  intros ? ? ? ih ?.
  set (p := ih (invmap (OrderedSet_univalence _ _) f)).
  set (h := homotweqinvweq (OrderedSet_univalence _ _) f).
  exact (transportf P h p).
Defined.

Ltac oset_induction f e := generalize f; apply OrderedSetEquivalence_rect; intro e; clear f.
  
(* standard ordered sets *)

Definition FiniteOrderedSet := Σ X:OrderedSet, isfinite X.
Definition underlyingOrderedSet (X:FiniteOrderedSet) : OrderedSet := pr1 X.
Coercion underlyingOrderedSet : FiniteOrderedSet >-> OrderedSet.
Definition finitenessProperty (X:FiniteOrderedSet) : isfinite X := pr2 X.

Definition standardFiniteOrderedSet (n:nat) : FiniteOrderedSet.
Proof.
  intros.
  refine (_,,_).
  { exists (stnposet n). split.
    { intros x y. apply istotalnatleh. }
    intros ? ? ? ?. apply isinjstntonat. now apply isantisymmnatleh. }
  { apply isfinitestn. }
Defined.

Local Notation "⟦ n ⟧" := (standardFiniteOrderedSet n) (at level 0).
(* in agda-mode \[[ n \]] *)

Definition FiniteStructure (X:OrderedSet) := Σ n, ⟦ n ⟧ ≅ X.

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

Theorem enumeration_FiniteOrderedSet (X:FiniteOrderedSet) : iscontr (FiniteStructure X).
Proof.
  intros.
  refine (_,,_).
  { exists (fincard (finitenessProperty X)).

Abort.


(** * computably ordered sets *)

(* Here we abstract from Chapter 11 of the HoTT book just the order
   properties of the real numbers, as constructed there. *)

Open Scope logic.

Definition isLattice {X:hSet} (le:hrel X) (min max:binop X) :=
  Σ po : ispo le,
  Σ lub : ∀ x y z, le x z ∧ le y z <-> le (max x y) z,
  Σ glb : ∀ x y t, le t x ∧ le t y <-> le t (min x y),
  Σ transle: ∀ x y z, le x y -> le y z -> le x z,
  unit.

Definition istrans2 {X:hSet} (le lt:hrel X) :=
  Σ transltle: ∀ x y z, lt x y -> le y z -> lt x z,
  Σ translelt: ∀ x y z, le x y -> lt y z -> lt x z,
  unit.

Definition iswklin {X} (lt:hrel X) := ∀ x y z, lt x y -> lt x z ∨ lt z y.

Goal ∀ X (lt:hrel X), iscotrans lt <-> iswklin lt.
Proof.
  intros. unfold iscotrans, iswklin. split.
  { intros i x1 x3 x2. apply i. }
  { intros i x z y. apply i. }
Defined.

Definition isComputablyOrdered {X:hSet}
           (lt:hrel X) (min max:binop X) := 
  let le x y := ¬ lt y x in
  Σ latt: isLattice le min max,
  Σ trans2: istrans2 le lt,
  Σ asymm: isasymm lt,          (* ? not on Andrej's list *)
  Σ translt: istrans lt,
  Σ irrefl: isirrefl lt,
  Σ cotrans: iscotrans lt,
  unit.

Local Theorem classical {X:hSet} (lt:hrel X) (min max:binop X) :
  let le x y := ¬ lt y x in
  isComputablyOrdered lt min max -> LEM -> istotal le.
Proof.      
  intros ? ? ? ? ?
         [[po[lub[glb[transle _]]]]
            [[transltle [translelt _]][asymm[translt[irrefl[cotrans _]]]]]] lem
  x y.
  apply hinhpr.
  induction (lem (le x y)) as [a|a].
  { now apply ii1. }
  induction (lem (le y x)) as [b|b].
  { now apply ii2. }
  assert (a' := dneg_LEM _ lem a); clear a.
  assert (b' := dneg_LEM _ lem b); clear b.
  induction (asymm _ _ a' b').
Defined.
