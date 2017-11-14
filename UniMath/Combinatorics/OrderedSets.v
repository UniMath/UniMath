(* -*- coding: utf-8 -*- *)

Require Import UniMath.Combinatorics.FiniteSets.
Unset Automatic Introduction.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Local Open Scope poset.

(** partially ordered sets and ordered sets *)

Definition isTotalOrder {X : hSet} (R : hrel X) : hProp
  := hProppair (isPartialOrder R × istotal R)
               (isapropdirprod _ _ (isaprop_isPartialOrder R) (isaprop_istotal R)).

Section A.

  Open Scope logic.

  Lemma tot_nge_to_le {X:hSet} (R:hrel X) : istotal R -> ∏ x y, ¬ (R x y) ->  R y x.
  Proof.
    intros ? ? tot ? ? nle.
    now apply (hdisjtoimpl (tot x y)).
  Defined.

  Lemma tot_nle_iff_gt {X:hSet} (R:hrel X) :
    isTotalOrder R -> ∏ x y, ¬ (R x y)  <->  R y x ∧ ¬ (y = x).
  (** if [R x y] is [x ≤ y], then this shows the equivalence of two definitions for [y < x] *)
  Proof.
    intros X R i.
    assert (tot := pr2 i); simpl in tot.
    assert (refl := pr2 (pr1 (pr1 i))); simpl in refl.
    assert (anti := pr2 (pr1 i)); simpl in anti.
    split.
    { intros nle. split.
      - now apply tot_nge_to_le.
      - intros ne. induction ne. exact (nle (refl y)). }
    { intros yltx xley. induction yltx as [ylex neq]. exact (neq (anti _ _ ylex xley)). }
  Defined.

End A.

Definition isSmallest {X : Poset} (x : X) : UU := ∏ y, x ≤ y.

Definition isBiggest {X : Poset} (x : X) : UU := ∏ y, y ≤ x.

Definition isMinimal {X : Poset} (x : X) : UU := ∏ y, y ≤ x -> x = y.
(* the definition in Sets.v is wrong *)

Definition isMaximal {X : Poset} (x : X) : UU := ∏ y, x ≤ y -> x = y.
(* the definition in Sets.v is wrong *)

Definition consecutive {X : Poset} (x y : X) : UU := x < y × ∏ z, ¬ (x < z × z < y).

Lemma isaprop_isSmallest {X : Poset} (x : X) : isaprop (isSmallest x).
Proof.
  intros. unfold isSmallest. apply impred_prop.
Defined.

Lemma isaprop_isBiggest {X : Poset} (x : X) : isaprop (isBiggest x).
Proof.
  intros. unfold isBiggest. apply impred_prop.
Defined.

Definition Poset_univalence_map {X Y:Poset} : X=Y -> PosetEquivalence X Y.
Proof. intros ? ? e. induction e. apply identityPosetEquivalence.
Defined.

Local Arguments isPosetEquivalence : clear implicits.
Local Arguments isaposetmorphism : clear implicits.

Lemma posetStructureIdentity {X:hSet} (R S:PartialOrder X) :
  @isPosetEquivalence (X,,R) (X,,S) (idweq X) <-> R=S.
Proof.
  intros. split.
  { intros e.
    apply subtypeEquality. { intros T. apply isaprop_isPartialOrder. }
    induction R as [R r]; induction S as [S s]; simpl.
    apply funextfun; intro x; apply funextfun; intro y.
    unfold isPosetEquivalence in e.
    unfold isaposetmorphism in e; simpl in e.
    induction e as [e e'].
    unfold posetRelation in *. unfold invmap in *; simpl in *.
    apply hPropUnivalence. { apply e. } { apply e'. } }
  { intros p. induction p. apply isPosetEquivalence_idweq. }
Defined.

Local Lemma posetTransport_weq (X Y:Poset) : X╝Y ≃ X≅Y.
Proof.
  intros. simple refine (weqbandf _ _ _ _).
  { apply hSet_univalence. }
  intros e. apply invweq. induction X as [X R], Y as [Y S]; simpl in e.
  induction e; simpl. apply weqimplimpl.
  { exact (pr1 (posetStructureIdentity R S)). }
  { exact (pr2 (posetStructureIdentity R S)). }
  { exact (isaprop_isPosetEquivalence _). }
  { exact (isaset_PartialOrder _ _ _). }
Defined.

Local Theorem Poset_univalence_0 (X Y:Poset) : X=Y ≃ X≅Y.
Proof.
  intros. intermediate_weq (X╝Y).
  - apply total2_paths_equiv.
  - apply posetTransport_weq.
Defined.

Lemma Poset_univalence_compute {X Y:Poset} (e:X=Y) :
  Poset_univalence_0 X Y e = Poset_univalence_map e.
Proof.
  try reflexivity.              (* fails, so we use "remakeweq" below *)
Abort.

Theorem Poset_univalence (X Y:Poset) : X=Y ≃ X≅Y.
Proof.
  intros.
  assert (k : pr1weq (Poset_univalence_0 X Y) ~ @Poset_univalence_map X Y).
  { intro e. apply isinj_pr1_PosetEquivalence. induction e. reflexivity. }
  exact (remakeweq k).
Defined.

Lemma Poset_univalence_compute {X Y:Poset} (e:X=Y) :
  Poset_univalence X Y e = Poset_univalence_map e.
Proof. reflexivity. Defined.

(* now we try to mimic this construction:

    Inductive PosetEquivalence (X Y:Poset) : Type :=
                  pathToEq : (X=Y) -> PosetEquivalence X Y.

    PosetEquivalence_rect
         : ∏ (X Y : Poset) (P : PosetEquivalence X Y -> Type),
           (∏ e : X = Y, P (pathToEq X Y e)) ->
           ∏ p : PosetEquivalence X Y, P p

*)

Theorem PosetEquivalence_rect (X Y : Poset) (P : X ≅ Y -> UU) :
  (∏ e : X = Y, P (Poset_univalence_map e)) -> ∏ f, P f.
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

Definition OrderedSet := ∑ X:Poset, istotal (posetRelation X).

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

Definition Poset_lessthan {X:Poset} (x y:X) := ∥ x ≤ y  ×  x != y ∥.

Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 60, no associativity) : oset.
Notation "m ≤ n" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "m <= n" := (posetRelation _ m n) (no associativity, at level 70) : oset.
Notation "m < n" := (Poset_lessthan m n) :oset.
Notation "n ≥ m" := (posetRelation _ m n) (no associativity, at level 70) : oset.
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
  assert (tot := OrderedSet_istotal x y).
  induction (deceq x y) as [j|j].
  - apply ii1. induction j. unwrap_OrderedSet X. apply refl.
  - assert (c : (y ≥ x) ⨿ (x ≥ y)).
    { assert (d : isaprop ((y ≥ x) ⨿ (x ≥ y))).
      { apply isapropcoprod.
        * apply propproperty.
        * apply propproperty.
        * intros r s. apply j; clear j. unwrap_OrderedSet X. now apply antisymm. }
      apply (squash_to_prop tot).
      + exact d.
      + intro e. exact e.
      }
    induction c as [c|c'].
    + now apply ii1.
    + apply ii2. intro le. apply j. now apply OrderedSet_isantisymm.
Defined.

Corollary isfinite_isdec_ordering (X:OrderedSet) : isfinite X -> isdec_ordering X.
Proof. intros ? i ? ?. apply isdeceq_isdec_ordering. now apply isfinite_isdeceq.
Defined.

Corollary isdeceq_isdec_lessthan (X:OrderedSet) :
  isdeceq X -> ∏ (x y:X), decidable (x < y).
Proof.
  intros ? i ? ?. unfold Poset_lessthan. apply decidable_ishinh. apply decidable_dirprod.
  - now apply isdeceq_isdec_ordering.
  - apply neg_isdecprop.
    apply isdecpropif.
    * apply setproperty.
    * apply i.
Defined.

Corollary isfinite_isdec_lessthan (X:OrderedSet) : isfinite X -> ∏ (x y:X), decidable (x < y).
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

Lemma smallestUniqueness (X:OrderedSet) (x y:X) : isSmallest x -> isSmallest y -> x = y.
Proof.
  intros ? ? ? i j. assert (q := OrderedSet_istotal x y). apply (squash_to_prop q).
  { apply setproperty. }
  intro c. induction c as [xley|ylex].
  - apply OrderedSet_isantisymm.
    + assumption.
    + now apply j.
  - apply OrderedSet_isantisymm.
    + now apply i.
    + assumption.
Defined.

Lemma biggestUniqueness (X:OrderedSet) (x y:X) : isBiggest x -> isBiggest y -> x = y.
Proof.
  intros ? ? ? i j. assert (q := OrderedSet_istotal x y). apply (squash_to_prop q).
  { apply setproperty. }
  intro c. induction c as [xley|ylex].
  - apply OrderedSet_isantisymm.
    + assumption.
    + now apply i.
  - apply OrderedSet_isantisymm.
    + now apply j.
    + assumption.
Defined.

Theorem OrderedSet_univalence (X Y:OrderedSet) : X=Y ≃ X≅Y.
Proof. intros. exact ((Poset_univalence _ _) ∘ (underlyingPoset_weq _ _))%weq.
Defined.

Theorem OrderedSetEquivalence_rect (X Y : OrderedSet) (P : X ≅ Y -> UU) :
  (∏ e : X = Y, P (OrderedSet_univalence _ _ e)) -> ∏ f, P f.
Proof.
  intros ? ? ? ih ?.
  set (p := ih (invmap (OrderedSet_univalence _ _) f)).
  set (h := homotweqinvweq (OrderedSet_univalence _ _) f).
  exact (transportf P h p).
Defined.

Ltac oset_induction f e := generalize f; apply OrderedSetEquivalence_rect; intro e; clear f.

(* standard ordered sets *)

Definition FiniteOrderedSet := ∑ X:OrderedSet, isfinite X.
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

Notation "x ≐ y" := (FiniteOrderedSetDecidableEquality _ x y) (at level 70, no associativity) : foset. (* in agda mode, \doteq *)
Notation "x ≠ y" := (FiniteOrderedSetDecidableInequality _ x y) (at level 70, no associativity) : foset. (* in agda mode, \ne *)
Notation " x ≤ y " := ( FiniteOrderedSetDecidableOrdering _ x y ) (at level 70, no associativity) : foset. (* in agda mode, \le *)
Notation " x <= y " := ( FiniteOrderedSetDecidableOrdering _ x y ) (at level 70, no associativity) : foset.
Notation " x ≥ y " := ( FiniteOrderedSetDecidableOrdering _ y x ) (at level 70, no associativity) : foset. (* in agda mode, \ge *)
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

Definition height_stn {X:FiniteOrderedSet} : X -> stn (cardinalityFiniteSet X).
Proof.
  intros ? x.
  exists (height x).



(* Defined. *)
Abort.

(** making finite ordered sets in various ways *)

Definition standardFiniteOrderedSet (n:nat) : FiniteOrderedSet.
Proof.
  intros. simple refine (_,,_).
  - exists (stnposet n). intros x y; apply istotalnatleh.
  - apply isfinitestn.
Defined.

Notation "⟦ n ⟧" := (standardFiniteOrderedSet n) (at level 50) : foset.
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
        exact (pr2 (pr2 (pr1 (pr1 (⟦ n ⟧))))).
    * intros x y. apply (pr2 (pr1 (⟦ n ⟧))).
  - simpl.
    apply (isfiniteweqb w).
    exact (pr2 (⟦ n ⟧)).
Defined.
Close Scope foset.

(** concatenating finite ordered families of finite ordered sets *)

Definition lexicographicOrder
           (X:hSet) (Y:X->hSet)
           (R:hrel X) (S : ∏ x, hrel (Y x)) : hrel (∑ x, Y x)%set.
  intros ? ? ? ? u u'.
  set (x := pr1 u). set (y := pr2 u). set (x' := pr1 u'). set (y' := pr2 u').
  exact ((x != x' × R x x') ∨ (∑ e : x = x', S x' (transportf Y e y) y')).
Defined.

Lemma lex_isrefl (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∏ x, hrel (Y x)) :
  (∏ x, isrefl(S x)) -> isrefl (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Srefl u. induction u as [x y]. apply hdisj_in2; simpl.
  exists (idpath x). apply Srefl.
Defined.

Lemma lex_istrans (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∏ x, hrel (Y x)) :
  isantisymm R -> istrans R -> (∏ x, istrans(S x)) -> istrans (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Ranti Rtrans Strans u u' u'' p q.
  induction u as [x y]. induction u' as [x' y']. induction u'' as [x'' y''].
  refine (p _ _); clear p; intro p; simpl in p.
  induction p as [p|p].
  - induction p as [pn pl].
    refine (q _ _); clear q; intro q; simpl in q.
    induction q as [q|q].
    + apply hinhpr; simpl.
      induction q as [qn ql].
      apply ii1. split. intro ne. induction ne.
      assert (k := Ranti x x' pl ql).
      contradicts pn k.
      exact (Rtrans x x' x'' pl ql).
    + induction q as [e l].
      apply hinhpr; simpl.
      apply ii1.
      induction e.
      exact (pn,,pl).
  - induction p as [e s].
    induction e; unfold transportf in s; simpl in s; unfold idfun in s.
    refine (q _ _); clear q; intro q; simpl in q.
    induction q as [q|q].
    + induction q as [n r].
      apply hdisj_in1; simpl.
      exact (n,,r).
    + induction q as [e' s']. induction e'.
      unfold transportf in s'; simpl in s'; unfold idfun in s'.
      apply hdisj_in2; simpl.
      exists (idpath x).
      exact (Strans x y y' y'' s s').
Defined.

Local Ltac unwrap a := apply (squash_to_prop a);
    [ apply isaset_total2_hSet | simpl; clear a; intro a; simpl in a ].

Lemma lex_isantisymm (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∏ x, hrel (Y x)) :
  isantisymm R -> (∏ x, isantisymm(S x)) -> isantisymm (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Ranti Santi u u' a b.
  induction u as [x y]; induction u' as [x' y'].
  unwrap a. unwrap b. induction a as [[m r]|a].
  - induction b as [[n s]|b].
    + assert (eq := Ranti x x' r s). contradicts m eq.
    + induction b as [eq s]. contradicts (!eq) m.
  - induction a as [eq s]. induction b as [[n r]|b].
    { contradicts n (!eq). }
    induction b as [eq' s']. assert ( c : eq = !eq' ).
    { apply setproperty. }
    induction (!c); clear c. induction eq'. assert ( t : y = y' ).
    { apply (Santi x' y y' s s'). }
    induction t. reflexivity.
Defined.

Lemma lex_istotal (X:hSet) (Y:X->hSet) (R:hrel X) (S : ∏ x, hrel (Y x)) :
  isdeceq X -> istotal R -> (∏ x, istotal(S x)) -> istotal (lexicographicOrder X Y R S).
Proof.
  intros ? ? ? ? Xdec Rtot Stot u u'. induction u as [x y]. induction u' as [x' y'].
  induction (Xdec x x') as [eq|ne].
  { refine (Stot x' (transportf Y eq y) y' _ _); intro P. induction P as [P|P].
    { apply hdisj_in1. unfold lexicographicOrder; simpl. apply hdisj_in2. exact (eq,,P). }
    { apply hdisj_in2. unfold lexicographicOrder; simpl. apply hdisj_in2.
      induction eq. exact (idpath _,,P). }}
  { refine (Rtot x x' _ _); intro P. induction P as [P|P].
    { apply hdisj_in1. apply hdisj_in1. simpl. exact (ne,,P). }
    { apply hdisj_in2. apply hdisj_in1. simpl. exact (ne ∘ pathsinv0,,P). }}
Defined.

Definition concatenateFiniteOrderedSets
           {X:FiniteOrderedSet} (Y:X->FiniteOrderedSet) : FiniteOrderedSet.
Proof.
  (* we use lexicographic order *)
  intros.
  simple refine (_,,_).
  {
    simple refine (_,,_).
    { simple refine (_,,_).
      { exact (∑ x, Y x)%set. }
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

Notation "'∑'  x .. y , P" := (concatenateFiniteOrderedSets (λ x, .. (concatenateFiniteOrderedSets (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : foset.
  (* type this in emacs in agda-input method with \sum *)

(** sorting finite ordered sets *)

Definition FiniteStructure (X:OrderedSet) := ∑ n, ⟦ n ⟧ %foset ≅ X.

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

Theorem isasetFiniteOrderedSet : isaset FiniteOrderedSet.
(* This theorem will be useful for formalizing simplicial objects, which are contravariant functors
  from the category [Ord] to another category.  There are two definitions of [Ord]: in the first,
  the set of objects in [nat].  In the second, the set of objects is the type of nonempty finite
  ordered sets.  This theorem is part of showing those definitions are equivalent.  The second
  definition is more convenient, for if A and B are objects, so is [coprod A B], where the elements
  of A come before the elements of B. *)
Proof.

Abort.

(** * computably ordered sets *)

(* Here we abstract from Chapter 11 of the HoTT book just the order
   properties of the real numbers, as constructed there. *)

Open Scope logic.

Definition isLattice {X:hSet} (le:hrel X) (min max:binop X) :=
  ∑ po : isPartialOrder le,
  ∑ lub : ∏ x y z, le x z ∧ le y z <-> le (max x y) z,
  ∑ glb : ∏ x y t, le t x ∧ le t y <-> le t (min x y),
  unit.

Definition istrans2 {X:hSet} (le lt:hrel X) :=
  ∑ transltle: ∏ x y z, lt x y -> le y z -> lt x z,
  ∑ translelt: ∏ x y z, le x y -> lt y z -> lt x z,
  unit.

Definition iswklin {X} (lt:hrel X) := ∏ x y z, lt x y -> lt x z ∨ lt z y.

Definition isComputablyOrdered {X:hSet}
           (lt:hrel X) (min max:binop X) :=
  let le x y := ¬ lt y x in
  ∑ latt: isLattice le min max,
  ∑ trans2: istrans2 le lt,
  ∑ translt: istrans lt,
  ∑ irrefl: isirrefl lt,
  ∑ cotrans: iscotrans lt,
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
    refine (n _); clear n.
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
        refine (l _ _); intro m; clear l.
        induction m as [n|o].
        * apply hdisj_in2; apply hdisj_in2; exact n.
        * apply hdisj_in1; exact o.
    Defined.

    Local Lemma le_istotal : istotal le.
    Proof.
      intros x y.
      assert (m := trichotomy x y).
      refine (m _ _); clear m; intro m; induction m as [m|m].
      - apply hdisj_in1. apply lt_implies_le. exact m.
      - refine (m _ _); clear m; intro m; induction m as [m|m].
        * apply hdisj_in1. induction m. unfold le. expand ic. apply irrefl.
        * apply hdisj_in2. apply lt_implies_le. exact m.
    Defined.

  End ClassicalProperties.

End OtherProperties.
