(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets.
Unset Automatic Introduction.
Require Import UniMath.Foundations.FunctionalExtensionality.
Local Open Scope poset.
Local Notation "● x" := (x,,idpath _) (at level 35).

(* propositions, move upstream *)

Lemma subsetFiniteness {X} (is : isfinite X) (P : DecidableSubtype X) :
  isfinite (underlyingType P).
Proof.
  intros.
  assert (fin : isfinite (underlyingType' P)).
  { now apply isfinitedecsubset. }
  refine (isfiniteweqf _ fin).
  apply underlyingType_weq.
Defined.

Definition subsetFiniteSet {X:FiniteSet} (P:DecidableSubtype X) : FiniteSet.

Definition fincard_subset {X} (is : isfinite X) (P : DecidableSubtype X) : nat.
Proof. intros ? fin ?. exact (fincard (subsetFiniteness fin P)). Defined.

Definition fincard_standardSubset {n} (P : DecidableSubtype (stn n)) : nat.
Proof. intros. exact (fincard (subsetFiniteness (isfinitestn n) P)). Defined.

Goal 3 = fincard_standardSubset (λ i:stn 10, 2*i <? 6). Proof. reflexivity. Defined.

Coercion underlyingType : DecidableSubtype >-> UU.

Local Definition bound01 (P:DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  intros. unfold choice. choose P p q; exact nopathsfalsetotrue.
Defined.

Definition tallyStandardSubset {n} (P: DecidableSubtype (stn n)) : stn (S n).
Proof. intros. exists (stnsum (λ x, choice (P x) 1 0)). apply natlehtolthsn.
       apply istransnatleh with (m := stnsum(λ _ : stn n, 1)).
       { apply stnsum_le; intro i. apply bound01. }
       assert ( p : ∀ r s, r = s -> (r ≤ s)%nat). { intros ? ? e. destruct e. apply isreflnatleh. }
       apply p. apply stnsum_1.
Defined.

Goal 3 = tallyStandardSubset (λ i:stn 10, 2*i <? 6). Proof. reflexivity. Defined.

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

Lemma posetStructureIdentity {X:hSet} (R S:PartialOrder X) :
  @isPosetEquivalence (X,,R) (X,,S) (idweq X) -> R=S.
Proof.
  intros ? ? ? e.
  apply total2_paths_second_isaprop. { apply isaprop_isPartialOrder. }
  induction R as [R r]; induction S as [S s]; simpl.
  apply funextfun; intro x; apply funextfun; intro y.
  unfold isPosetEquivalence in e.
  unfold isaposetmorphism in e; simpl in e.
  induction e as [e e'].
  unfold posetRelation in *. unfold invmap in *; simpl in *.
  apply uahp. { apply e. } { apply e'. }
Defined.

Open Scope transport_scope.

Lemma poTransport_logeq {X Y:hSet} (R:PartialOrder X) (S:PartialOrder Y) (f:X=Y) :
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f)
  <-> f#R = S.
Proof.
  split.
  { intros i. induction f. apply posetStructureIdentity. apply i. }
  { intros e. induction f. induction e. apply isPosetEquivalence_idweq. }
Defined.

Corollary poTransport_weq {X Y:hSet} (R:PartialOrder X) (S:PartialOrder Y) (f:X=Y) :
  @isPosetEquivalence (X,,R) (Y,,S) (hSet_univalence_map _ _ f)
  ≃ f#R = S.
Proof.
  intros. apply weqimplimpl.
  { apply (pr1 (poTransport_logeq _ _ _)). }
  { apply (pr2 (poTransport_logeq _ _ _)). }
  { apply isaprop_isPosetEquivalence. }
  { apply isaset_PartialOrder. }
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

Definition OrderedSet := Σ X:Poset, istotal (posetRelation X).

Ltac unwrap_OrderedSet X :=
  induction X as [X total];
  induction X as [X _po_];
  induction _po_ as [R _i_];
  unwrap_isPartialOrder _i_;
  unfold posetRelation in total;
  simpl in total.

Local Definition underlyingPoset (X:OrderedSet) : Poset := pr1 X.
Coercion underlyingPoset : OrderedSet >-> Poset.

Delimit Scope oset with oset.

Definition Poset_lessthan {X:Poset} (x y:X) := (x ≤ y) ∧ (hneg (x = y)).

Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 60, no associativity) : oset.
Notation "m ≤ n" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "m < n" := (Poset_lessthan m n) :oset.

Close Scope poset.
Local Open Scope oset.

Definition OrderedSet_isrefl {X:OrderedSet} (x:X) : x ≤ x.
Proof. intros. unwrap_OrderedSet X; simpl in x. apply refl. Qed.

Definition OrderedSet_isantisymm {X:OrderedSet} (x y:X) : x ≤ y -> y ≤ x -> x = y.
Proof. intros ? ? ? r s. unwrap_OrderedSet X; simpl in x, y. now apply antisymm. Qed.

Definition OrderedSet_istotal {X:OrderedSet} (x y:X): x ≤ y ∨ y ≤ x :=
  pr2 X x y.

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
Proof. apply isinclpr1. intros X. apply isaprop_istotal. Defined.

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

Lemma FiniteOrderedSet_isdec_ordering (X:FiniteOrderedSet) : isdec_ordering X.
Proof. intros. apply isfinite_isdec_ordering. apply finitenessProperty. Defined.
Abort.

Definition FiniteSetDecidableOrdering (X:FiniteOrderedSet) : DecidableRelation X.
Proof.
  intros ? x y.
  assert (k := FiniteOrderedSet_isdec_ordering X x y).
  unfold decidable in k.

  (* exact (DecidableProposition_pair ). *)
Abort.

Definition FiniteOrderedSet_segment (X:FiniteOrderedSet) (x:X) : FiniteSet.
Proof.
  intros.
Abort.


Definition standardFiniteOrderedSet (n:nat) : FiniteOrderedSet.
Proof.
  intros. refine (_,,_).
  - exists (stnposet n). intros x y; apply istotalnatleh.
  - apply isfinitestn.
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
  Σ po : isPartialOrder le,
  Σ lub : ∀ x y z, le x z ∧ le y z <-> le (max x y) z,
  Σ glb : ∀ x y t, le t x ∧ le t y <-> le t (min x y),
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
  Σ translt: istrans lt,
  Σ irrefl: isirrefl lt,
  Σ cotrans: iscotrans lt,
  unit.

Local Ltac expand ic :=
  induction ic as
    [[[[transle reflle]antisymmle][lub[glb _]]]
       [[transltle [translelt _]][translt[irrefl[cotrans _]]]]].

Section OtherProperties.

  Variable (X:hSet)
            (lt:hrel X)
            (min max:binop X)
            (ic:isComputablyOrdered lt min max).

  Let le x y := ¬ lt y x.
  Let apart x y := lt y x ∨ lt x y.
  Let eq x y := @eqset X x y.
  Let ne x y := hneg (eq x y).

  Local Lemma apart_isirrefl : isirrefl apart.
  Proof.
    expand ic.
    intros x a.
    unfold apart in a.
    apply (a hfalse); clear a; intros b.
    induction b as [b|b]; exact (irrefl _ b).
  Defined.

  Local Lemma lt_implies_le x y : lt x y -> le x y.
  Proof.
    intros ? ? l.
    intro m.
    expand ic.
    assert (n := translt _ _ _ l m).
    exact (irrefl _ n).
  Qed.

  Local Lemma apart_implies_ne x y : apart x y -> ne x y.
  Proof.
    expand ic.
    intros ? ? a e.
    induction e.
    apply (apart_isirrefl _ a).
  Defined.

  Local Lemma tightness x y : ¬ apart x y <-> x = y.
  Proof.
    expand ic. 
    split.
    - intro m. assert (p := fromnegcoprod_prop m); clear m.
      induction p as [p q]. now apply antisymmle.
    - intro e. induction e. apply apart_isirrefl.
  Defined.

  Local Lemma ne_implies_dnegapart x y : ne x y -> ¬¬ apart x y.
  Proof.
    intros ? ? n m.
    apply n; clear n.
    now apply tightness.
  Defined.

  Section ClassicalProperties.

    Variable lem:LEM.

    Local Lemma ne_implies_apart x y : ne x y -> apart x y.
    Proof.
      intros ? ? a.
      apply (dneg_LEM _ lem).
      now apply ne_implies_dnegapart.
    Defined.

    Local Lemma trichotomy x y : lt x y ∨ eq x y ∨ lt y x.
    Proof.
      intros.
      induction (lem (eq x y)) as [a|b].
      - apply hdisj_in2; apply hdisj_in1; exact a.
      - assert (l := ne_implies_apart _ _ b); clear b.
        unfold apart in l.
        apply l; intro m; clear l.
        induction m as [n|o].
        * apply hdisj_in2; apply hdisj_in2; exact n.
        * apply hdisj_in1; exact o.
    Defined.

    Local Lemma le_istotal : istotal le.
    Proof.
      intros x y.
      assert (m := trichotomy x y).
      apply m; clear m; intro m; induction m as [m|m].
      - apply hdisj_in1. apply lt_implies_le. exact m.
      - apply m; clear m; intro m; induction m as [m|m].
        * apply hdisj_in1. induction m. unfold le. expand ic. apply irrefl.
        * apply hdisj_in2. apply lt_implies_le. exact m.
    Defined.

  End ClassicalProperties.

End OtherProperties.

