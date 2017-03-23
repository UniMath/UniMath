(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.DecidablePropositions.

Local Open Scope logic.
Local Open Scope prop.
Local Open Scope set.
Local Open Scope subtype.
Local Open Scope poset.

Delimit Scope tosubset with tosubset. (* subsets equipped with a well ordering *)
Local Open Scope tosubset.

Delimit Scope wosubset with wosubset. (* subsets equipped with a well ordering *)
Local Open Scope wosubset.

Definition TotalOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isTotalOrder R.

Definition TOSubset_set (X:hSet) : hSet := ∑ (S:subtype_set X), TotalOrdering (carrier_set S).

Definition TOSubset (X:hSet) : UU := TOSubset_set X.

Definition TOSubset_to_subtype {X:hSet} : TOSubset X -> hsubtype X
  := pr1.

Coercion TOSubset_to_subtype : TOSubset >-> hsubtype.

Local Definition TOrel {X:hSet} (S : TOSubset X) : hrel (carrier S) := pr12 S.

Notation "s ≤ s'" := (TOrel _ s s') : tosubset.

Definition TOtotal {X:hSet} (S : TOSubset X) : istotal (TOrel S).
Proof.
  apply (pr2 S).
Defined.

Definition TOanti {X:hSet} (S : TOSubset X) : isantisymm (TOrel S).
Proof.
  apply (pr2 S).
Defined.

Definition TOrefl {X:hSet} (S : TOSubset X) : isrefl (TOrel S).
Proof.
  apply (pr2 S).
Defined.

Definition TOeq_to_refl {X:hSet} (S : TOSubset X) : ∀ s t : carrier_set S, s = t ⇒ s ≤ t.
Proof.
  intros s t e. induction e. apply TOrefl.
Defined.

Definition TOtrans {X:hSet} (S : TOSubset X) : istrans (TOrel S).
Proof.
  apply (pr2 S).
Defined.

Local Lemma h1'' {X} {S:TOSubset X} {r s t u:S} : (r ≤ t -> pr1 r = pr1 s -> pr1 t = pr1 u -> s ≤ u)%tosubset.
Proof.
  intros le p q.
  assert (p' : r = s).
  { now apply subtypeEquality_prop. }
  assert (q' : t = u).
  { now apply subtypeEquality_prop. }
  induction p', q'. exact le.
Defined.

Definition tosub_order_compat {X:hSet} {S T : TOSubset X} (le : S ⊆ T) : hProp
  := ∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s'.

Definition tosub_le (X:hSet) (S T : TOSubset X) : hProp
  := (∑ le : S ⊆ T, tosub_order_compat le)%prop.

Notation "S ≼ T" := (tosub_le _ S T) (at level 70) : tosubset.

Definition sub_initial {X:hSet} (S : hsubtype X) (T : TOSubset X) (le : S ⊆ T) : hProp
  := ∀ (s t : X) (Ss : S s) (Tt : T t), TOrel T (t,,Tt) (s,,le s Ss) ⇒ S t.

Definition contained_initial {X:hSet} (B : hsubtype X) (S : TOSubset X) : hProp
  := ∃ le : B ⊆ S, sub_initial B S le.

Lemma filter_sub_initial_2 {X:hSet} (B C : hsubtype X) (S : TOSubset X)
      (i : contained_initial B S) (j : contained_initial C S) :
  ∀ x y, B x ⇒ (C y ⇒ C x ∨ B y).
Proof.
  intros x y Bx Cy.
  apply (squash_to_hProp i); clear i; intros [le si].
  apply (squash_to_hProp j); clear j; intros [le' sj].
  apply (squash_to_hProp (TOtotal S (x,,le x Bx) (y,,le' y Cy))).
  intros c. apply hinhpr. induction c as [c|c].
  -                             (* x ≤ y, so both are in C *)
    apply ii1. use sj.
    + exact y.
    + assumption.
    + now use le.
    + assumption.
  -                             (* y ≤ x, so both are in B *)
    apply ii2. use si.
    + exact x.
    + assumption.
    + now use le'.
    + assumption.
Defined.

Lemma hdisj_3 (P Q R : hProp) : P ⨿ Q ⨿ R -> P ∨ Q ∨ R.
(* upstream *)
Proof.
  intros [[p|q]|r].
  - exact (hinhpr (ii1 p)).
  - exact (hinhpr (ii2 (hinhpr (ii1 q)))).
  - exact (hinhpr (ii2 (hinhpr (ii2 r)))).
Defined.

Axiom oops : ∏ X, X.

Lemma filter_sub_initial_3 {X:hSet} (B C D : hsubtype X) (S : TOSubset X)
      (i : contained_initial B S) (j : contained_initial C S) (k : contained_initial D S) :
  ∀ x y z, B x ⇒ (C y ⇒ (D z ⇒ (D x ∧ D y  ∨  C x ∧ C z  ∨  B y ∧ B z))).
(* This is interesting, because it's constructive, whereas proving one of B, C, D contains
   the others involves proof by contradiction. *)
Proof.
  intros x y z Bx Cy Dz.
  apply (squash_to_hProp i); clear i; intros [le si].
  apply (squash_to_hProp j); clear j; intros [le' sj].
  apply (squash_to_hProp k); clear k; intros [le'' sk].
  apply (squash_to_hProp (TOtotal S (x,,le x Bx) (y,,le' y Cy))); intros c.
  apply (squash_to_hProp (TOtotal S (x,,le x Bx) (z,,le'' z Dz))); intros c'.
  apply (squash_to_hProp (TOtotal S (y,,le' y Cy) (z,,le'' z Dz))); intros c''.
  apply hdisj_3.
  induction c as [c|c], c' as [c'|c'], c'' as [c''|c''].
  -                             (* x,y ≤ z, so all are in D *)
    apply ii1. apply ii1. split.
    + use sk.
      * exact z.
      * assumption.
      * now use le.
      * assumption.
    + use sk.
      * exact z.
      * assumption.
      * now use le'.
      * assumption.
  -                             (* x,z ≤ y, so all are in C *)
    apply ii1. apply ii2. split.
    + use sj.
      * exact y.
      * assumption.
      * now use le.
      * assumption.
    + use sj.
      * exact y.
      * assumption.
      * now use le''.
      * assumption.
  -                             (* x ≤ y ≤ z ≤ x, so x=y=z and any will do *)
    apply ii1. apply ii2. split.
    + use sj.
      * exact y.
      * assumption.
      * now use le.
      * assumption.
    + use sj.
      * exact x.
      * use sj.
        ** exact y.
        ** assumption.
        ** now use le.
        ** assumption.
      * now use le''.
      * now apply (h1'' c').
  -                             (* x,z ≤ y, so all are in C *)
    apply ii1. apply ii2. split.
    + use sj.
      * exact y.
      * assumption.
      * now use le.
      * assumption.
    + use sj.
      * exact y.
      * assumption.
      * now use le''.
      * assumption.
  -                             (* x,y ≤ z, so all are in D *)
    apply ii1. apply ii1. split.
    + use sk.
      * exact z.
      * assumption.
      * now use le.
      * assumption.
    + use sk.
      * exact z.
      * assumption.
      * now use le'.
      * assumption.
  -                             (* z ≤ y ≤ x ≤ z, so x=y=z and any would do *)
    apply ii1. apply ii2. split.
    + use sj.
      * exact z.
      * use sj.
        ** exact y.
        ** assumption.
        ** now use le''.
        ** assumption.
      * now use le.
      * now apply (h1'' c').
    + use sj.
      * exact y.
      * assumption.
      * now use le''.
      * assumption.
  -                             (* y,z ≤ x, so al are in B *)
    apply ii2. split.
    + use si.
      * exact x.
      * assumption.
      * now use le'.
      * assumption.
    + use si.
      * exact x.
      * assumption.
      * now use le''.
      * assumption.
  -                             (* y,z ≤ x *)
    apply ii2. split.
    + use si.
      * exact x.
      * assumption.
      * now use le'.
      * assumption.
    + use si.
      * exact x.
      * assumption.
      * now use le''.
      * assumption.
Defined.

Definition same_induced_ordering {X:hSet} {S T : TOSubset X} {B : hsubtype X} (BS : B ⊆ S) (BT : B ⊆ T)
  := ∀ x y : B,
             subtype_inc BS x ≤ subtype_inc BS y
                         ⇔
             subtype_inc BT x ≤ subtype_inc BT y.

Definition common_initial {X:hSet} (B : hsubtype X) (S T : TOSubset X) :=
  ∃ (BS : B ⊆ S) (BT : B ⊆ T), sub_initial B S BS ∧ sub_initial B T BT ∧ same_induced_ordering BS BT.

(* the largest initial common ordered subset of S and of T, as the union of all of them *)
Definition max_sub_initial {X:hSet} (S T : TOSubset X) : hsubtype X
  := λ x, ∃ (B : hsubtype X), B x ∧ common_initial B S T.

(* Lemma max_sub_initial_is_max {X:hSet} *)
(*       (S T : TOSubset X) (A : hsubtype X) (AS : A ⊆ S) (AT : A ⊆ T) : *)
(*   common_initial AS AT -> A ⊆ max_sub_initial S T. *)
(* Proof. *)
(*   intros AST x Ax. exact (hinhpr(A,,AS,,AT,,Ax,,AST)). *)
(* Defined. *)

(* Lemma max_sub_initial_is_sub {X:hSet} (S T : TOSubset X) : *)
(*   max_sub_initial S T ⊆ S ∧ max_sub_initial S T ⊆ T. *)
(* Proof. *)
(*   split. *)
(*   - intros x m. apply (squash_to_hProp m); intros [B [BS [_ [Bx _]]]]; clear m. exact (BS _ Bx). *)
(*   - intros x m. apply (squash_to_hProp m); intros [B [_ [BT [Bx _]]]]; clear m. exact (BT _ Bx). *)
(* Defined. *)

(* Lemma max_sub_initial_is_common_initial {X:hSet} (S T : TOSubset X) : *)
(*   common_initial (pr1 (max_sub_initial_is_sub S T)) (pr2 (max_sub_initial_is_sub S T)). *)
(* Proof. *)
(*   split. *)
(*   { intros x s le. induction x as [x xm]. *)
(*     apply (squash_to_hProp xm); intros [B [BS [BT [Bx [BSi [BTi BST]]]]]]. *)
(*     assert (Q := BSi (x,,Bx) s); simpl in Q. *)
(*     assert (E : subtype_inc (pr1 (max_sub_initial_is_sub S T)) (x,, xm) = subtype_inc BS (x,, Bx)). *)
(*     { now apply subtypeEquality_prop. } *)
(*     induction E. assert (Q' := Q le); clear Q le. *)
(*     exact (hinhpr(B,,BS,,BT,,Q',,BSi,,BTi,,BST)). } *)
(*   split. *)
(*   { intros x t le. induction x as [x xm]. *)
(*     apply (squash_to_hProp xm); intros [B [BS [BT [Bx [BSi [BTi BST]]]]]]. *)
(*     assert (Q := BTi (x,,Bx) t); simpl in Q. *)
(*     assert (E : subtype_inc (pr2 (max_sub_initial_is_sub S T)) (x,, xm) = subtype_inc BT (x,, Bx)). *)
(*     { now apply subtypeEquality_prop. } *)
(*     induction E. assert (Q' := Q le); clear Q le. *)
(*     exact (hinhpr(B,,BS,,BT,,Q',,BSi,,BTi,,BST)). } *)
(*   split. *)
(*   {                             (* why did the variables x, x0 get introduced here?? *) *)
(*     generalize x0; clear x0; intros y. *)
(*     intros le. *)


(* Abort. *)

Lemma tosub_fidelity {X:hSet} {S T:TOSubset X} (le : S ≼ T)
      (s s' : S) : s ≤ s' ⇔ subtype_inc (pr1 le) s ≤ subtype_inc (pr1 le) s'.
Proof.
  split.
  { exact (pr2 le s s'). }
  { intro l. apply (squash_to_hProp (TOtotal S s s')). intros [c|c].
    - exact c.
    - apply (TOeq_to_refl S s s'). assert (k := pr2 le _ _ c); clear c.
      assert (k' := TOanti T _ _ l k); clear k l.
      apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
Defined.

Definition hasSmallest {X : UU} (R : hrel X) : hProp
  := ∀ S : hsubtype X, (∃ x, S x) ⇒ ∃ x:X, S x ∧ ∀ y:X, S y ⇒ R x y.

Lemma iswellordering_istotal {X : hSet} (R : hrel X) : hasSmallest R -> istotal R.
Proof.
  intros has x y.
  (* make the doubleton subset containing x and y and its two elements *)
  set (S := λ z, z=x ∨ z=y).
  assert (xinS := hinhpr (ii1 (idpath _)) : S x). assert (yinS := hinhpr (ii2 (idpath _)) : S y).
  assert (h := hinhpr(x,,xinS) : ∃ s, S s). assert (q := has S h); clear h has.
  apply (squash_to_hProp q); clear q; intro q.
  induction q as [s min], min as [sinS smin].
  apply (squash_to_hProp sinS); clear sinS. intro d. apply hinhpr. induction d as [d|d].
  - induction (!d); clear d. apply ii1. exact (smin _ yinS).
  - induction (!d); clear d. apply ii2. exact (smin _ xinS).
Defined.

Lemma actualSmallest {X : hSet} (R : hrel X) (S : hsubtype X) :
  isantisymm R -> hasSmallest R -> (∃ s, S s) -> ∑ s:X, S s ∧ ∀ t:X, S t ⇒ R s t.
(* antisymmetry ensures the smallest element of S is unique, so it actually exists *)
Proof.
  intros antisymm min ne. apply (squash_to_prop (min S ne)).
  { apply invproofirrelevance; intros s t. apply subtypeEquality_prop.
    induction s as [x i], t as [y j], i as [I i], j as [J j]. change (x=y)%set.
    apply (squash_to_hProp (iswellordering_istotal R min x y)). intros [c|c].
    { apply antisymm. { exact c. } { exact (j x I). } }
    { apply antisymm. { exact (i y J). } { exact c. } } }
  intros c. exact c.
Defined.

Definition isWellOrder {X : hSet} (R : hrel X) : hProp := isTotalOrder R ∧ hasSmallest R.

Definition WellOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isWellOrder R.

Definition WOSubset_set (X:hSet) : hSet := ∑ (S:subtype_set X), WellOrdering (carrier_set S).

Definition WOSubset (X:hSet) : UU := WOSubset_set X.

Definition WOSubset_to_subtype {X:hSet} : WOSubset X -> hsubtype X
  := pr1.

Coercion WOSubset_to_subtype : WOSubset >-> hsubtype.

Definition WOSubset_to_TOSubset {X:hSet} : WOSubset X -> TOSubset X.
Proof.
  intros S. exists (pr1 S). exists (pr12 S). exact (pr122 S).
Defined.

Coercion WOSubset_to_TOSubset : WOSubset >-> TOSubset.

Local Definition WOrel {X:hSet} (S : WOSubset X) : hrel (carrier S) := pr12 S.

Notation "s ≤ s'" := (WOrel _ s s') : wosubset.

Local Definition lt {X:hSet} {S : WOSubset X} (s s' : S) := ¬ (s' ≤ s)%wosubset.

Notation "s < s'" := (lt s s') : wosubset.

Definition wosub_le (X:hSet) : hrel (WOSubset X)
  := (λ S T : WOSubset X, ∑ (le : S ⊆ T), @tosub_order_compat _ S T le ∧ @sub_initial _ S T le)%prop.

Notation "S ≼ T" := (wosub_le _ S T) (at level 70) : wosubset.

Lemma wosub_le_isrefl {X:hSet} : isrefl (wosub_le X).
Proof.
  intros S.
  use tpair.
  + intros x xinS. exact xinS.
  + split.
    * intros s s' le. exact le.
    * intros s s' Ss Ss' le. exact Ss'.
Defined.

Definition wosub_equal {X:hSet} : hrel (WOSubset X) := λ S T, S ≼ T ∧ T ≼ S.

Notation "S ≣ T" := (wosub_equal S T) (at level 70) : wosubset.

Definition wosub_comparable {X:hSet} : hrel (WOSubset X) := λ S T, S ≼ T ∨ T ≼ S.

Lemma wosub_compare {X:hSet} {S T U : WOSubset X} :
  S ≼ U -> T ≼ U -> wosub_comparable S T.
Proof.
  intros su tu.


Abort.

Definition wosub_univalence_map {X:hSet} (S T : WOSubset X) : (S = T) -> (S ≣ T).
Proof.
  intros e. induction e. unfold wosub_equal.
  simple refine ((λ L, dirprodpair L L) _).
  use tpair.
  + intros x s. assumption.
  + split.
    * intros s s' le. assumption.
    * intros s t Ss St le. assumption.
Defined.

Theorem wosub_univalence {X:hSet} (S T : WOSubset X) : (S = T) ≃ (S ≣ T).
Proof.
  simple refine (remakeweq _).
  { unfold wosub_equal.
    intermediate_weq (S ╝ T).
    - apply total2_paths_equiv.
    - intermediate_weq (∑ e : S ≡ T, S ≼ T ∧ T ≼ S)%prop.
      + apply weqbandf.
        * apply hsubtype_univalence.
        * intro p. induction S as [S v], T as [T w]. simpl in p. induction p.
          change (v=w ≃ (S,, v ≼ S,, w ∧ S,, w ≼ S,, v)).
          induction v as [v i], w as [w j].
          intermediate_weq (v=w)%type.
          { apply subtypeInjectivity. change (isPredicate (λ R : hrel (carrier_set S), isWellOrder R)).
            intros R. apply propproperty. }
          apply weqimplimpl.
          { intros p. induction p. split.
            { use tpair.
              { intros s. change (S s → S s). exact (idfun _). }
              { split.
                { intros s s' le. exact le. }
                { intros s t Ss St le. exact St. } } }
            { use tpair.
              { intros s. change (S s → S s). exact (idfun _). }
              { split.
                { intros s s' le. exact le. }
                { intros s t Ss St le. exact St. } } } }
          { simpl. unfold WOrel. simpl. intros [[a [b _]] [d [e _]]].
            assert (triv : ∏ (f:∏ x : X, S x → S x) (x:carrier_set S), subtype_inc f x = x).
            { intros f s. apply subtypeEquality_prop. reflexivity. }
            apply funextfun; intros s. apply funextfun; intros t.
            apply hPropUnivalence.
            { intros le. assert (q := b s t le). rewrite 2 triv in q. exact q. }
            { intros le. assert (q := e s t le). rewrite 2 triv in q. exact q. } }
          { apply setproperty. }
          { apply propproperty. }
      + apply weqimplimpl.
        { intros k. split ; apply k. }
        { intros c. split.
          { intros x. exact (pr11 c x,,pr12 c x). }
          { exact c. } }
        { apply propproperty. }
        { apply propproperty. } }
  { apply wosub_univalence_map. }
  { intros e. induction e. reflexivity. }
Defined.

Lemma wosub_univalence_compute {X:hSet} (S T : WOSubset X) (e : S = T) :
  wosub_univalence S T e = wosub_univalence_map S T e.
Proof.
  reflexivity.
Defined.

Definition wosub_inc {X} {S T : WOSubset X} : (S ≼ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (pr1 le) s).
Defined.

Lemma wosub_fidelity {X:hSet} {S T:WOSubset X} (le : S ≼ T)
      (s s' : S) : s ≤ s' ⇔ wosub_inc le s ≤ wosub_inc le s'.
(* we want this lemma available after showing the union of a chain is totally ordered
   but before showing it has the smallest element condition *)
Proof.
  set (Srel := pr12 S).
  assert (Stot : istotal Srel).
  { apply (pr2 S). }
  set (Trel := pr12 T).
  assert (Tanti : isantisymm Trel).
  { apply (pr2 T). }
  split.
  { intro l. exact (pr12 le s s' l). }
  { intro l. apply (squash_to_hProp (Stot s s')).
    change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
    intro c. induction c as [c|c].
    - exact c.
    - induction le as [le [com ini]].
      assert (k := com s' s c).
      assert (k' := Tanti _ _ l k); clear k.
      assert (p : s = s').
      { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
      induction p. apply (pr2 S). (* refl *) }
Defined.

Local Lemma h1 {X} {S:WOSubset X} {s t u:S} : s = t -> t ≤ u -> s ≤ u.
Proof.
  intros p le. induction p. exact le.
Defined.

Lemma wosub_le_isPartialOrder X : isPartialOrder (wosub_le X).
Proof.
  repeat split.
  - intros S T U i j.
    exists (pr11 (subtype_containment_isPartialOrder X) S T U (pr1 i) (pr1 j)).
    split.
    + intros s s' l. exact (pr12 j _ _ (pr12 i _ _ l)).
    + intros s u Ss Uu l.
      change (hProptoType ((u,,Uu) ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) (s,,Ss)))) in l.
      set (uinT := u ,, pr22 j s u (pr1 i s Ss) Uu l : T).
      assert (p : subtype_inc (pr1 j) uinT = u,,Uu).
      { now apply subtypeEquality_prop. }
      assert (q := h1 p l : subtype_inc (pr1 j) uinT ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) (s,,Ss))).
      assert (r := pr2 (wosub_fidelity j _ _) q).
      assert (b := pr22 i _ _ _ _ r); simpl in b.
      exact b.
  - apply wosub_le_isrefl.
  - intros S T i j. apply (invmap (wosub_univalence _ _)). exact (i,,j).
Defined.

Definition WosubPoset (X:hSet) : Poset.
Proof.
  exists (WOSubset_set X).
  exists (λ S T, S ≼ T).
  exact (wosub_le_isPartialOrder X).
Defined.

Definition wosub_le_smaller {X:hSet} (S T:WOSubset X) : hProp := (S ≼ T) ∧ (∃ t:T, t ∉ S).

Notation "S ≺ T" := (wosub_le_smaller S T) (at level 70) : wosubset.

(* [upto s x] means x is in S and, as an element of S, it is strictly less than s *)
Definition upto {X:hSet} {S:WOSubset X} (s:S) : hsubtype X
  := (λ x, ∑ h:S x, (x,,h) < s)%prop.

Definition isInterval {X:hSet} (S T:WOSubset X) :
  isDecidablePredicate S -> S ≺ T -> ∃ t:T, S ≡ upto t.
Proof.
  set (R := WOrel T).
  assert (min : hasSmallest R).
  { apply (pr2 T). }
  intros dec lt.
  induction lt as [le ne].
  set (U := (λ t:T, t ∉ S) : hsubtype (carrier T)).
  assert (ne' : nonempty (carrier U)).
  { apply (squash_to_hProp ne); intro u. apply hinhpr. exact u. }
  clear ne. assert (minU := min U ne'); clear min ne'.
  apply (squash_to_hProp minU); clear minU; intros minU.
  induction minU as [u minu]. fold (WOSubset_to_subtype T) in u.
  induction minu as [uinU minu].
  (* minu says that u is the smallest element of T not in S *)
  apply hinhpr. exists u. intro y. split.
  - intro yinS. set (s := (y ,, yinS) : S). set (s' := subtype_inc (pr1 le) s).
    exists (pr2 s'). set (y' := y ,, pr2 s'). intro ules.
    assert (q := pr22 le _ _ _ _ ules); clear ules.
    simple refine (uinU _). exact q.
  - intro yltu. induction yltu as [yinT yltu].
    (* Goal : [S y].  We know y is smaller than the smallest element of T not in S,
       so at best, constructively, we know [¬ ¬ (S y)].  So prove it by contradiction. *)
    apply (decidable_proof_by_contradiction (dec _)).
    intro bc. simple refine (yltu _). simple refine (minu _ _). exact bc.
Defined.

(** Our goal now is to equip the union of a chain of subsets-with-well-orderings
    with a well ordering. *)

Definition is_wosubset_chain {X : hSet} {I : UU} (S : I → WOSubset X)
  := ∀ i j : I, wosub_comparable (S i) (S j).

Lemma common_index {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (i : I) (x : carrier_set (⋃ (λ i, S i))) :
   ∃ j, S i ≼ S j ∧ S j (pr1 x).
Proof.
  induction x as [x xinU]. apply (squash_to_hProp xinU); intros [k xinSk].
  change (∃ j : I, S i ≼ S j ∧ S j x).
  apply (squash_to_hProp (chain i k)). intros c. apply hinhpr. induction c as [c|c].
  - exists k. split.
    + exact c.
    + exact xinSk.
  - exists i. split.
    + apply wosub_le_isrefl.
    + exact (pr1 c x xinSk).
Defined.

Lemma common_index2 {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (x y : carrier_set (⋃ (λ i, S i))) :
   ∃ i, S i (pr1 x) ∧ S i (pr1 y).
Proof.
  induction x as [x j], y as [y k]. change (∃ i, S i x ∧ S i y).
  apply (squash_to_hProp j). clear j. intros [j s].
  apply (squash_to_hProp k). clear k. intros [k t].
  apply (squash_to_hProp (chain j k)). clear chain. intros [c|c].
  - apply hinhpr. exists k. split.
    + exact (pr1 c x s).
    + exact t.
  - apply hinhpr. exists j. split.
    + exact s.
    + exact (pr1 c y t).
Defined.

Lemma common_index3 {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (x y z : carrier_set (⋃ (λ i, S i))) :
   ∃ i, S i (pr1 x) ∧ S i (pr1 y) ∧ S i (pr1 z).
Proof.
  induction x as [x j], y as [y k], z as [z l]. change (∃ i, S i x ∧ S i y ∧ S i z).
  apply (squash_to_hProp j). clear j. intros [j s].
  apply (squash_to_hProp k). clear k. intros [k t].
  apply (squash_to_hProp l). clear l. intros [l u].
  apply (squash_to_hProp (chain j k)). intros [c|c].
  - apply (squash_to_hProp (chain k l)). clear chain. intros [d|d].
    + apply hinhpr. exists l. repeat split.
      * exact (pr1 d x (pr1 c x s)).
      * exact (pr1 d y t).
      * exact u.
    + apply hinhpr. exists k. repeat split.
      * exact (pr1 c x s).
      * exact t.
      * exact (pr1 d z u).
  - apply (squash_to_hProp (chain j l)). clear chain. intros [d|d].
    + apply hinhpr. exists l. repeat split.
      * exact (pr1 d x s).
      * exact (pr1 d y (pr1 c y t)).
      * exact u.
    + apply hinhpr. exists j. repeat split.
      * exact s.
      * exact (pr1 c y t).
      * exact (pr1 d z u).
Defined.

Lemma chain_union_prelim_eq0 {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S)
           (x y : X) (i j: I) (xi : S i x) (xj : S j x) (yi : S i y) (yj : S j y) :
  WOrel (S i) (x ,, xi) (y ,, yi) = WOrel (S j) (x ,, xj) (y ,, yj).
Proof.
  apply weqlogeq.
  apply (squash_to_hProp (chain i j)). intros [c|c].
  - split.
    + intro l. assert (q := pr12 c _ _ l); clear l. now apply (h1'' q).
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xi) (y,,yi))).
      now apply (@h1'' X (S j) _ _ _ _ l).
  - split.
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xj) (y,,yj))).
      now apply (@h1'' X (S i) _ _ _ _ l).
    + intro l. assert (q := pr12 c _ _ l); clear l. now apply (h1'' q).
Defined.

Definition chain_union_rel {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  hrel (carrier_set (⋃ (λ i, S i))).
Proof.
  intros x y.
  change (hPropset). simple refine (squash_to_hSet _ _ (common_index2 chain x y)).
  - intros [i [s t]]. exact (WOrel (S i) (pr1 x,,s) (pr1 y,,t)).
  - intros i j. now apply chain_union_prelim_eq0.
Defined.

Definition chain_union_rel_eqn {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S)
           (x y : carrier_set (⋃ (λ i, S i)))
           i (s : S i (pr1 x)) (t : S i (pr1 y)) :
  chain_union_rel chain x y = WOrel (S i) (pr1 x,,s) (pr1 y,,t).
Proof.
  unfold chain_union_rel. generalize (common_index2 chain x y); intro h.
  assert (e : hinhpr (i,,s,,t) = h).
  { apply propproperty. }
  now induction e.
Defined.

Lemma chain_union_rel_istrans {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  istrans (chain_union_rel chain).
Proof.
  intros x y z l m.
  apply (squash_to_hProp (common_index3 chain x y z)); intros [i [r [s t]]].
  assert (p := chain_union_rel_eqn chain x y i r s).
  assert (q := chain_union_rel_eqn chain y z i s t).
  assert (e := chain_union_rel_eqn chain x z i r t).
  rewrite p in l; clear p.
  rewrite q in m; clear q.
  rewrite e; clear e.
  assert (tot : istrans (WOrel (S i))).
  { apply (pr2 (S i)). }
  exact (tot _ _ _ l m).
Defined.

Lemma chain_union_rel_isrefl {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isrefl (chain_union_rel chain).
Proof.
  intros x. apply (squash_to_hProp (pr2 x)). intros [i r].
  assert (p := chain_union_rel_eqn chain x x i r r). rewrite p; clear p. apply (pr2 (S i)).
Defined.

Lemma chain_union_rel_isantisymm {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isantisymm (chain_union_rel chain).
Proof.
  intros x y l m.
  change (x=y)%set.
  apply (squash_to_hProp (common_index2 chain x y)); intros [i [r s]].
  apply subtypeEquality_prop.
  assert (p := chain_union_rel_eqn chain x y i r s). rewrite p in l; clear p.
  assert (q := chain_union_rel_eqn chain y x i s r). rewrite q in m; clear q.
  assert (anti : isantisymm (WOrel (S i))).
  { apply (pr2 (S i)). }
  assert (b := anti _ _ l m); clear anti l m.
  exact (maponpaths pr1 b).
Defined.

Lemma chain_union_rel_istotal {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  istotal (chain_union_rel chain).
Proof.
  intros x y.
  apply (squash_to_hProp (common_index2 chain x y)); intros [i [r s]].
  assert (p := chain_union_rel_eqn chain x y i r s). rewrite p; clear p.
  assert (p := chain_union_rel_eqn chain y x i s r). rewrite p; clear p.
  apply (pr2 (S i)).
Defined.

Definition chain_union_TOSubset {X : hSet} {I : UU} {S : I → WOSubset X}
           (Schain : is_wosubset_chain S) : TOSubset X.
Proof.
  exists (⋃ S).
  exists (chain_union_rel Schain).
  repeat split.
  - apply chain_union_rel_istrans.
  - apply chain_union_rel_isrefl.
  - apply chain_union_rel_isantisymm.
  - apply chain_union_rel_istotal.
Defined.

Notation "⋃ chain" := (chain_union_TOSubset chain) (at level 100, no associativity) : tosubset.

Lemma chain_union_tosub_le {X : hSet} {I : UU} {S : I → WOSubset X}
      (Schain : is_wosubset_chain S) (i:I)
      (inc := subtype_inc (subtype_union_containedIn S i)) :
  ( S i ≼ ⋃ Schain ) % tosubset.
Proof.
  exists (subtype_union_containedIn S i).
  intros s s' j.
  set (u := subtype_inc (λ x J, hinhpr (i,, J)) s : ⋃ Schain).
  set (u':= subtype_inc (λ x J, hinhpr (i,, J)) s': ⋃ Schain).
  change (chain_union_rel Schain u u').
  assert (q := chain_union_rel_eqn Schain u u' i (pr2 s) (pr2 s')).
  rewrite q; clear q. exact j.
Defined.

Lemma chain_union_rel_initial {X : hSet} {I : UU} {S : I → WOSubset X}
      (Schain : is_wosubset_chain S) (i:I)
      (inc := subtype_inc (subtype_union_containedIn S i)) :
    (∀ s:S i, ∀ t:⋃ Schain, t ≤ inc s ⇒ t ∈ S i)%tosubset.
Proof.
  intros s t le.
  apply (squash_to_hProp (common_index Schain i t)).
  intros [j [[ij [com ini]] tinSj]]. set (t' := (pr1 t,,tinSj) : S j). unfold sub_initial in ini.
  assert (K := ini (pr1 s) (pr1 t') (pr2 s) (pr2 t')); simpl in K. change (t' ≤ subtype_inc ij s → t ∈ S i) in K.
  apply K; clear K. unfold tosub_order_compat in com.
  apply (pr2 (tosub_fidelity (chain_union_tosub_le Schain j) t' (subtype_inc ij s))).
  clear com ini.
  assert (p : t = subtype_inc (pr1 (chain_union_tosub_le _ j)) t').
  { now apply subtypeEquality_prop. }
  induction p.
  assert (q : inc s = subtype_inc (pr1 (chain_union_tosub_le Schain j)) (subtype_inc ij s)).
  { now apply subtypeEquality_prop. }
  induction q.
  exact le.
Defined.

Lemma chain_union_rel_hasSmallest {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  hasSmallest (chain_union_rel chain).
Proof.
  intros T t'.
  apply (squash_to_hProp t'); clear t'; intros [[x i] xinT].
  apply (squash_to_hProp i); intros [j xinSj].
  induction (ishinh_irrel ( j ,, xinSj ) i).
  (* T' is the intersection of T with S j *)
  set (T' := (λ s, T (subtype_inc (subtype_union_containedIn S j) s))).
  assert (t' := hinhpr ((x,,xinSj),,xinT) : ∥ carrier T' ∥); clear x xinSj xinT.
  assert (min := pr222 (S j) T' t').
  apply (squash_to_hProp min); clear min t'; intros [t0 [t0inT' t0min]].
  (* t0 is the minimal element of T' *)
  set (t0' := subtype_inc (subtype_union_containedIn S j) t0).
  apply hinhpr. exists t0'. split.
  - exact t0inT'.
  - intros t tinT.
    (* now show any other element t of T is at least as big as t0' *)
    (* for that purpose, we may assume t ≤ t0' *)
    apply (hdisj_impl_2 (chain_union_rel_istotal chain _ _)); intro tle.
    set (q := chain_union_rel_initial chain j t0 t tle).
    set (t' := (pr1 t,,q) : S j).
    assert (E : subtype_inc (subtype_union_containedIn S j) t' = t).
    { now apply subtypeEquality_prop. }
    rewrite <- E. unfold t0'.
    apply (pr2 (chain_union_tosub_le chain j) t0 t'). apply (t0min t').
    unfold T'. rewrite E. exact tinT.
Defined.

Lemma chain_union_WOSubset {X:hSet} {I:UU} {S : I -> WOSubset X} (Schain : is_wosubset_chain S)
  : WOSubset X.
Proof.
  exists (⋃ Schain). exists (chain_union_rel Schain).
  repeat split.
  - apply chain_union_rel_istrans.
  - apply chain_union_rel_isrefl.
  - apply chain_union_rel_isantisymm.
  - apply chain_union_rel_istotal.
  - apply chain_union_rel_hasSmallest.
Defined.

Notation "⋃ chain" := (chain_union_WOSubset chain) (at level 100, no associativity) : wosubset.

Lemma chain_union_le {X:hSet} {I:UU} (S : I -> WOSubset X) (Schain : is_wosubset_chain S) :
  ∀ i, S i ≼ ⋃ Schain.
Proof.
  intros i. exists (subtype_union_containedIn S i). split.
  * exact (pr2 (chain_union_tosub_le _ i)).
  * intros s t Ss Tt.
    exact (chain_union_rel_initial Schain i (s,,Ss) (t,,Tt)).
Defined.

Definition proper_subtypes_set (X:UU) : hSet := ∑ S : subtype_set X, ∃ x, ¬ (S x).

(* the interval up to c, as a proper subset of X *)
Definition upto' {X:hSet} {C:WOSubset X} (c:C) : proper_subtypes_set X.
Proof.
  exists (upto c). apply hinhpr. exists (pr1 c). intro n.
  simpl in n. induction n as [n o]. apply o; clear o.
  apply (TOeq_to_refl C _ _). now apply subtypeEquality_prop.
Defined.

Theorem ZermeloWellOrdering {X:hSet} : AxiomOfChoice ⇒ ∃ R : hrel X, isWellOrder R.
(* see http://www.math.illinois.edu/~dan/ShortProofs/WellOrdering.pdf *)
Proof.
  intros ac. assert (lem := AC_to_LEM ac).
  (* for each proper subset S of X, pick an element [g(S)] in its complement *)
  apply (squash_to_hProp (ac (proper_subtypes_set X) (λ S, ∑ x, ¬ (pr1 S x)) pr2));
    intro g; change (∏ S : proper_subtypes_set X, ∑ x, ¬ (pr1 S x))%type in g.
  (* some well ordered subsets of X are called "g-sets" : *)
  set (isa_g_set := (λ C, ∀ c:C, pr1 c = pr1 (g (upto' c))) : WOSubset X -> hProp).
  assert (tot : ∏ C D, isa_g_set C -> isa_g_set D -> C ≼ D ∨ D ≼ C).
  { intros C D gC gD.
    set (W := max_sub_initial C D).




Admitted.