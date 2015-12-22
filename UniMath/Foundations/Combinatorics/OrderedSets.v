(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.Combinatorics.FiniteSets.
Unset Automatic Introduction.
Require Import UniMath.Foundations.Basics.UnivalenceAxiom.
Local Open Scope poset.

Lemma subsetFiniteness {X} (is : isfinite X) (P : DecidableSubtype X) :
  isfinite (decidableSubtypeCarrier P).
Proof.
  intros.
  assert (fin : isfinite (decidableSubtypeCarrier' P)).
  { now apply isfinitedecsubset. }
  refine (isfiniteweqf _ fin).
  apply decidableSubtypeCarrier_weq.
Defined.

Definition subsetFiniteSet {X:FiniteSet} (P:DecidableSubtype X) : FiniteSet.
Proof. intros X P. exact (isfinite_to_FiniteSet (subsetFiniteness (pr2 X) P)). Defined.

Definition fincard_subset {X} (is : isfinite X) (P : DecidableSubtype X) : nat.
Proof. intros ? fin ?. exact (fincard (subsetFiniteness fin P)). Defined.

Definition fincard_standardSubset {n} (P : DecidableSubtype (stn n)) : nat.
Proof. intros. exact (fincard (subsetFiniteness (isfinitestn n) P)). Defined.

Local Definition bound01 (P:DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  intros. unfold choice. choose P p q; reflexivity.
Defined.

Definition tallyStandardSubset {n} (P: DecidableSubtype (stn n)) : stn (S n).
Proof. intros. exists (stnsum (λ x, choice (P x) 1 0)). apply natlehtolthsn.
       apply (istransnatleh (m := stnsum(λ _ : stn n, 1))).
       { apply stnsum_le; intro i. apply bound01. }
       assert ( p : ∀ r s, r = s -> (r ≤ s)%nat). { intros ? ? e. destruct e. apply isreflnatleh. }
       apply p. apply stnsum_1.
Defined.

Definition tallyStandardSubsetSegment {n} (P: DecidableSubtype (stn n))
           (i:stn n) : stn n.
  (* count how many elements less than i satisfy P *)
  intros.
  assert (k := tallyStandardSubset
                 (λ j:stn i, P (stnincl i n (natlthtoleh i n (pr2 i)) j))).
  apply (stnincl (S i) n).
  { apply natlthtolehsn. exact (pr2 i). }
  exact k.
Defined.

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
  apply subtypeEquality. { intros T. apply isaprop_isPartialOrder. }
  induction R as [R r]; induction S as [S s]; simpl.
  apply funextfun; intro x; apply funextfun; intro y.
  unfold isPosetEquivalence in e.
  unfold isaposetmorphism in e; simpl in e.
  induction e as [e e'].
  unfold posetRelation in *. unfold invmap in *; simpl in *.
  apply uahp. { apply e. } { apply e'. }
Defined.

Open Scope transport.

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
  simple refine (weqbandf _ _ _ _).
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
Notation "m <= n" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "m < n" := (Poset_lessthan m n) :oset.
Notation "n \ge m" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "n >= m" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "n > m" := (Poset_lessthan m n) :oset.

Close Scope poset.
Local Open Scope oset.

Definition OrderedSet_isrefl {X:OrderedSet} (x:X) : x ≤ x.
Proof. intros. unwrap_OrderedSet X; simpl in x. apply refl. Defined.

Definition OrderedSet_isantisymm {X:OrderedSet} (x y:X) : x ≤ y -> y ≤ x -> x = y.
Proof. intros ? ? ? r s. unwrap_OrderedSet X; simpl in x, y. now apply antisymm. Defined.

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
  intros. simple refine (weqpair _ _).
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
Definition underlyingFiniteSet : FiniteOrderedSet -> FiniteSet.
Proof. intros. exists X. apply finitenessProperty. Defined.
Coercion underlyingFiniteSet : FiniteOrderedSet >-> FiniteSet.

Lemma istotal_FiniteOrderedSet (X:FiniteOrderedSet) : istotal (posetRelation X).
Proof. intros. exact (pr2 (pr1 X)). Defined.

Lemma FiniteOrderedSet_isdeceq {X:FiniteOrderedSet} : isdeceq X.
Proof. intros. apply isfinite_isdeceq. apply finitenessProperty. Defined.

Lemma FiniteOrderedSet_isdec_ordering {X:FiniteOrderedSet} : isdec_ordering X.
Proof. intros. apply isfinite_isdec_ordering. apply finitenessProperty. Defined.

Definition FiniteOrderedSetDecidableOrdering (X:FiniteOrderedSet) : DecidableRelation X :=
  λ (x y:X), decidable_to_DecidableProposition (FiniteOrderedSet_isdec_ordering x y).

Definition FiniteOrderedSetDecidableEquality (X:FiniteOrderedSet) : DecidableRelation X :=
  λ (x y:X), @decidable_to_DecidableProposition (eqset x y) (FiniteOrderedSet_isdeceq x y).

Definition FiniteOrderedSetDecidableInequality (X:FiniteOrderedSet) : DecidableRelation X.
  intros ? x y.
  apply (@decidable_to_DecidableProposition (¬ (x = y)))%logic.
  unfold decidable; simpl.
  apply neg_isdecprop.
  apply decidable_to_isdecprop_2.
  { apply setproperty. }
  apply FiniteOrderedSet_isdeceq.
Defined.

Definition FiniteOrderedSetDecidableLessThan (X:FiniteOrderedSet) : DecidableRelation X.
  intros ? x y. simple refine (decidable_to_DecidableProposition _).
  - exact (x < y).
  - apply isfinite_isdec_lessthan. apply finitenessProperty.
Defined.

Notation "x = y" := (FiniteOrderedSetDecidableEquality _ x y) (at level 70, no associativity) : foset.
Notation "x ≠ y" := (FiniteOrderedSetDecidableInequality _ x y) (at level 70, no associativity) : foset.
Notation " x ≤ y " := ( FiniteOrderedSetDecidableOrdering _ x y ) (at level 70, no associativity) : foset.
Notation " x <= y " := ( FiniteOrderedSetDecidableOrdering _ x y ) (at level 70, no associativity) : foset.
Notation " x ≥ y " := ( FiniteOrderedSetDecidableOrdering _ y x ) (at level 70, no associativity) : foset.
Notation " x >= y " := ( FiniteOrderedSetDecidableOrdering _ y x ) (at level 70, no associativity) : foset.
Notation " x < y " := ( FiniteOrderedSetDecidableLessThan _ x y ) (at level 70, no associativity) : foset.
Notation " x > y " := ( FiniteOrderedSetDecidableLessThan _ y x ) (at level 70, no associativity) : foset.

Delimit Scope foset with foset.

Definition FiniteOrderedSet_segment {X:FiniteOrderedSet} (x:X) : FiniteSet.
  intros. apply (@subsetFiniteSet X); intro y. exact (y < x)%foset.
Defined.

Definition height {X:FiniteOrderedSet} : X -> nat.
  intros ? x. exact (cardinalityFiniteSet (FiniteOrderedSet_segment x)).
Defined.

(** making finite ordered sets in various ways *)

Definition standardFiniteOrderedSet (n:nat) : FiniteOrderedSet.
Proof.
  intros. simple refine (_,,_).
  - exists (stnposet n). intros x y; apply istotalnatleh.
  - apply isfinitestn.
Defined.

Notation "⟦ n ⟧" := (standardFiniteOrderedSet n) (at level 0) : foset.
(* in agda-mode \[[ n \]] *)

Lemma inducedPartialOrder {X Y} (f:X->Y) (incl:isInjective f) (R:hrel Y) (po:isPartialOrder R) :
  isPartialOrder (λ x x' : X, R (f x) (f x')).
Proof.
  intros.
  split.
  - split.
    * intros x y z a b. exact (pr1 (pr1 po) (f x) (f y) (f z) a b).
    * intros x. exact (pr2 (pr1 po) (f x)).
  - intros x y a b. apply incl. exact (pr2 po (f x) (f y) a b).
Defined.

Corollary inducedPartialOrder_weq {X Y} (f:X≃Y) (R:hrel Y) (po:isPartialOrder R) :
  isPartialOrder (λ x x' : X, R (f x) (f x')).
Proof. intros. exact (inducedPartialOrder f (incl_injectivity  f (weqproperty f)) R po). Defined.

Local Open Scope foset.
Definition transportFiniteOrdering {n} {X:UU} : X ≃ ⟦ n ⟧ -> FiniteOrderedSet.
(* The new finite ordered set has X as its underlying set. *)
Proof.
  intros ? ? w.
  simple refine (_,,_).
  - simple refine (_,,_).
    * simple refine (_,,_).
    + exists X. apply (isofhlevelweqb 2 w). apply setproperty.
      + unfold PartialOrder; simpl. simple refine (_,,_).
        { intros x y. exact (w x ≤ w y). }
        apply inducedPartialOrder_weq.
        exact (pr2 (pr2 (pr1 (pr1 ⟦ n ⟧)))).
    * intros x y. apply (pr2 (pr1 ⟦ n ⟧)).
  - simpl.
    apply (isfiniteweqb w).
    exact (pr2 ⟦ n ⟧).
Defined.
Close Scope foset.

(** concatenating finite ordered families of finite ordered sets *)

Definition total2_hSet {X:hSet} (Y:X->hSet) : hSet := hSetpair (Σ x, Y x) (isaset_total2 X Y).

Notation "'Σ'  x .. y , P" := (total2_hSet (fun x => .. (total2_hSet (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : set.
  (* type this in emacs in agda-input method with \Sigma *)

Definition lexicographicOrder
           (X:hSet) (Y:X->hSet)
           (R:hrel X) (S : ∀ x, hrel (Y x)) : hrel (Σ x, Y x)%set.
  intros ? ? ? ? u u'.
  set (x := pr1 u). set (y := pr2 u). set (x' := pr1 u'). set (y' := pr2 u').
  exact ((x != x' ∧ R x x') ∨ (∃ e : x = x', S x' (transportf Y e y) y'))%set.
Defined.

Lemma lex_isrefl (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∀ x, hrel (Y x)) :
  (∀ x, isrefl(S x)) -> isrefl (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Srefl u. induction u as [x y]. apply hdisj_in2; simpl.
  apply hinhpr. exists (idpath x). apply Srefl.
Defined.

Lemma lex_istrans (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∀ x, hrel (Y x)) :
  isantisymm R -> istrans R -> (∀ x, istrans(S x)) -> istrans (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Ranti Rtrans Strans u u' u'' p q.
  induction u as [x y]. induction u' as [x' y']. induction u'' as [x'' y''].
  apply p; clear p; intro p; simpl in p.
  induction p as [p|p].
  - induction p as [pn pl].
    apply q; clear q; intro q; simpl in q.
    induction q as [q|q].
    + apply hinhpr; simpl.
      induction q as [qn ql].
      apply ii1. split. intro ne. induction ne.
      assert (k := Ranti x x' pl ql).
      contradicts pn k.
      exact (Rtrans x x' x'' pl ql).
    + apply q; clear q; intro q; simpl in q. induction q as [e l].
      apply hinhpr; simpl.
      apply ii1.
      induction e.
      exact (pn,,pl).
  - apply p; clear p; intro p. induction p as [e s].
    induction e; unfold transportf in s; simpl in s; unfold idfun in s.
    apply q; clear q; intro q; simpl in q.
    induction q as [q|q].
    + induction q as [n r].
      apply hdisj_in1; simpl.
      exact (n,,r).
    + apply q; clear q; intro q. induction q as [e' s']. induction e'.
      unfold transportf in s'; simpl in s'; unfold idfun in s'.
      apply hdisj_in2; simpl. apply hinhpr.
      exists (idpath x).
      exact (Strans x y y' y'' s s').
Defined.

Local Ltac unwrap a := apply (squash_to_prop a); [ apply isaset_total2 | simpl; clear a; intro a; simpl in a ].

Lemma lex_isantisymm (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∀ x, hrel (Y x)) :
  isantisymm R -> (∀ x, isantisymm(S x)) -> isantisymm (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Ranti Santi u u' a b.
  induction u as [x y]; induction u' as [x' y'].
  unwrap a. unwrap b. induction a as [[m r]|a].
  - induction b as [[n s]|b].
    + assert (eq := Ranti x x' r s). contradicts m eq.
    + unwrap b. induction b as [eq s]. contradicts (!eq) m.
  - unwrap a. induction a as [eq s]. induction b as [[n r]|b].
    { contradicts n (!eq). }
    unwrap b. induction b as [eq' s']. assert ( c : eq = !eq' ).
    { apply setproperty. }
    induction (!c); clear c. induction eq'. assert ( t : y = y' ).
    { apply (Santi x' y y' s s'). }
    induction t. reflexivity. Defined.

Lemma lex_istotal (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∀ x, hrel (Y x)) :
  isdeceq X -> istotal R -> (∀ x, istotal(S x)) -> istotal (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Xdec Rtot Stot u u'. induction u as [x y]. induction u' as [x' y'].
  induction (Xdec x x') as [eq|ne].
  { apply (Stot x' (transportf Y eq y) y'); intro P. induction P as [P|P].
    { apply hdisj_in1. unfold lexicographicOrder; simpl. apply hdisj_in2. apply hinhpr. exact (eq,,P). }
    { apply hdisj_in2. unfold lexicographicOrder; simpl. apply hdisj_in2. apply hinhpr.
      induction eq. exact (idpath _,,P). }}
  { apply (Rtot x x'); intro P. induction P as [P|P].
    { apply hdisj_in1. apply hdisj_in1. simpl. exact (ne,,P). }
    { apply hdisj_in2. apply hdisj_in1. simpl. exact (ne ∘ pathsinv0,,P). }} Defined.

Definition concatenateFiniteOrderedSets
           {X:FiniteOrderedSet} (Y:X->FiniteOrderedSet) : FiniteOrderedSet.
Proof.
  (* we use lexicographic order *)
  intros.
  simple refine (_,,_).
  {
    simple refine (_,,_).
    { simple refine (_,,_).
      { exact (Σ x, Y x)%set. }
      simple refine (_,,_).
      { apply lexicographicOrder. apply posetRelation. intro. apply posetRelation. }
      split.
      { split.
        { apply lex_istrans.
          { apply isantisymm_posetRelation. }
          { apply istrans_posetRelation. }
          { intro. apply istrans_posetRelation. } }
        apply lex_isrefl.
        intro; apply isrefl_posetRelation. }
      apply lex_isantisymm.
      { apply isantisymm_posetRelation. }
      intro. apply isantisymm_posetRelation. }
    apply lex_istotal.
    { apply FiniteOrderedSet_isdeceq. }
    { apply istotal_FiniteOrderedSet. }
    intro; apply istotal_FiniteOrderedSet. }
  apply isfinitetotal2.
  { apply finitenessProperty. }
  intro; apply finitenessProperty.
Defined.

Notation "'Σ'  x .. y , P" := (concatenateFiniteOrderedSets (fun x => .. (concatenateFiniteOrderedSets (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : foset.
  (* type this in emacs in agda-input method with \Sigma *)

(** sorting finite ordered sets *)

Definition FiniteStructure (X:OrderedSet) := Σ n, ⟦ n ⟧ %foset ≅ X.

Local Lemma std_auto n : iscontr (⟦ n ⟧ ≅ ⟦ n ⟧) %foset.
Proof.
  intros. exists (identityPosetEquivalence _). intros f.
  apply subtypeEquality.
  { intros g. apply isaprop_isPosetEquivalence. }
  simpl. apply isinjpr1weq. simpl. apply funextfun. intros i.

  (* proof in progress... *)

Abort.

Lemma isapropFiniteStructure X : isaprop (FiniteStructure X).
Proof.
  intros.
  apply invproofirrelevance; intros r s.
  destruct r as [m p].
  destruct s as [n q].
  apply subtypePairEquality.
  {
    intros k.
    apply invproofirrelevance; intros [[r b] i] [[s c] j]; simpl in r,s,i,j.

    (* proof in progress... *)

    admit.
    }
  {
    apply weqtoeqstn.
    exact (weqcomp (pr1 p) (invweq (pr1 q))).
  }
Abort.

Theorem enumeration_FiniteOrderedSet (X:FiniteOrderedSet) : iscontr (FiniteStructure X).
Proof.
  intros.
  simple refine (_,,_).
  { exists (fincard (finitenessProperty X)).

  (* proof in progress... *)

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
  Defined.

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
