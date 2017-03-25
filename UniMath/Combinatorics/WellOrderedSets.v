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

(** ** Totally ordered subsets of a set *)

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

Definition TOeq_to_refl_1 {X:hSet} (S : TOSubset X) : ∀ s t : carrier_set S, pr1 s = pr1 t ⇒ s ≤ t.
Proof.
  intros s t e. assert (E : s = t).
  { now apply subtypeEquality_prop. }
  clear e. induction E. apply TOrefl.
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

Definition same_induced_ordering {X:hSet} {S T : TOSubset X} {B : hsubtype X} (BS : B ⊆ S) (BT : B ⊆ T)
  := ∀ x y : B,
             subtype_inc BS x ≤ subtype_inc BS y
                         ⇔
             subtype_inc BT x ≤ subtype_inc BT y.

Definition common_initial {X:hSet} (B : hsubtype X) (S T : TOSubset X) : hProp
  := (∑ (BS : B ⊆ S) (BT : B ⊆ T), sub_initial B S BS ∧ sub_initial B T BT ∧ same_induced_ordering BS BT)%prop.

(* the largest initial common ordered subset of S and of T, as the union of all of them *)
Definition max_common_initial {X:hSet} (S T : TOSubset X) : hsubtype X
  := λ x, ∃ (B : hsubtype X), B x ∧ common_initial B S T.

Lemma max_common_initial_is_max {X:hSet} (S T : TOSubset X) (A : hsubtype X) :
  common_initial A S T -> A ⊆ max_common_initial S T.
Proof.
  intros c x Ax. exact (hinhpr (A,,Ax,,c)).
Defined.

Lemma max_common_initial_is_sub {X:hSet} (S T : TOSubset X) :
  max_common_initial S T ⊆ S
  ∧
  max_common_initial S T ⊆ T.
Proof.
  split.
  - intros x m. apply (squash_to_hProp m); intros [B [Bx [BS [_ _]]]]; clear m. exact (BS _ Bx).
  - intros x m. apply (squash_to_hProp m); intros [B [Bx [_ [BT _]]]]; clear m. exact (BT _ Bx).
Defined.

Local Lemma h1' {X} {S:TOSubset X} {s t u:S} : s ≤ t -> pr1 t = pr1 u -> s ≤ u.
Proof.
  intros le p.
  assert (q : t = u).
  { now apply subtypeEquality_prop. }
  induction q. exact le.
Defined.

Lemma max_common_initial_is_common_initial {X:hSet} (S T : TOSubset X) :
  common_initial (max_common_initial S T) S T.
Proof.
  exists (pr1 (max_common_initial_is_sub S T)).
  exists (pr2 (max_common_initial_is_sub S T)).
  split.
  { intros x s M Ss le.
    apply (squash_to_hProp M); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    unfold sub_initial in BSi.
    apply hinhpr.
    exists B.
    split.
    + apply (BSi x s Bx Ss). now apply (h1' le).
    + exact (BS,,BT,,BSi,,BTi,,BST). }
  split.
  { intros x t M Tt le.
    apply (squash_to_hProp M); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    unfold sub_initial in BSi.
    apply hinhpr.
    exists B.
    split.
    + apply (BTi x t Bx Tt). now apply (h1' le).
    + exact (BS,,BT,,BSi,,BTi,,BST). }
  intros x y.
  split.
  { intros le. induction x as [x xm], y as [y ym].
    apply (squash_to_hProp xm); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    apply (squash_to_hProp ym); intros [C [Cy [CS [CT [CSi [CTi CST]]]]]].
    assert (Cx : C x).
    { apply (CSi y x Cy (BS x Bx)). now apply (h1'' le). }
    assert (Q := pr1 (CST (x,,Cx) (y,,Cy))); simpl in Q.
    assert (E : subtype_inc CS (x,, Cx) ≤ subtype_inc CS (y,, Cy)).
    { now apply (h1'' le). }
    clear le. now apply (h1'' (Q E)). }
  { intros le. induction x as [x xm], y as [y ym].
    apply (squash_to_hProp xm); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    apply (squash_to_hProp ym); intros [C [Cy [CS [CT [CSi [CTi CST]]]]]].
    assert (Cx : C x).
    { apply (CTi y x Cy (BT x Bx)). now apply (h1'' le). }
    assert (Q := pr2 (CST (x,,Cx) (y,,Cy))); simpl in Q.
    assert (E : subtype_inc CT (x,, Cx) ≤ subtype_inc CT (y,, Cy)).
    { now apply (h1'' le). }
    clear le. now apply (h1'' (Q E)). }
Defined.

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

(** ** Well ordered subsets of a set *)

Definition hasSmallest {X : UU} (R : hrel X) : hProp
  := ∀ S : hsubtype X, (∃ x, S x) ⇒ ∃ x:X, S x ∧ ∀ y:X, S y ⇒ R x y.

Definition isWellOrder {X : hSet} (R : hrel X) : hProp := isTotalOrder R ∧ hasSmallest R.

Definition WellOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isWellOrder R.

Definition WOSubset_set (X:hSet) : hSet := ∑ (S:subtype_set X), WellOrdering (carrier_set S).

Definition WOSubset (X:hSet) : UU := WOSubset_set X.

Definition WOSubset_to_subtype {X:hSet} : WOSubset X -> hsubtype X
  := pr1.

Definition WOSubset_to_TOSubset {X:hSet} : WOSubset X -> TOSubset X.
Proof.
  intros S. exists (pr1 S). exists (pr12 S). exact (pr122 S).
Defined.

Coercion WOSubset_to_TOSubset : WOSubset >-> TOSubset.

Local Definition WOrel {X:hSet} (S : WOSubset X) : hrel (carrier S) := pr12 S.

Notation "s ≤ s'" := (WOrel _ s s') : wosubset.

Local Definition lt {X:hSet} {S : WOSubset X} (s s' : S) := ¬ (s' ≤ s)%wosubset.

Notation "s < s'" := (lt s s') : wosubset.

Lemma wo_lt_to_le {X:hSet} {S : WOSubset X} (s s' : S) : s < s' -> s ≤ s'.
Proof.
  unfold lt.
  intros lt.
  apply (squash_to_hProp (TOtotal S s s')); intros [c|c].
  - exact c.
  - exact (fromempty (lt c)).
Defined.

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

Lemma upto_eqn {X:hSet} {S T:WOSubset X} (x:X) (Sx : S x) (Tx : T x) :
  S ≼ T -> upto (x,,Sx) = upto (x,,Tx).
Proof.
  intros ST.
  apply (invmap (hsubtype_univalence _ _)).
  intros y.
  split.
  - intros [Sy lt].
    exists (pr1 ST y Sy).
    generalize lt; clear lt.
    apply negf.
    intros le'.
    apply (pr2 (wosub_fidelity ST (x,, Sx) (y,, Sy))).
    now apply (h1'' (S := T) le').
  - intros [Ty lt].
    assert (Q := pr22 ST x y Sx Ty); simpl in Q.
    assert (e : pr1 ST x Sx = Tx).
    { apply propproperty. }
    induction e.
    assert (Sy := Q (wo_lt_to_le _ _ lt) : S y); clear Q.
    exists Sy.
    generalize lt; clear lt.
    apply negf.
    intros le'.
    now apply (h1'' (pr12 ST _ _ le')).
Defined.

Definition isInterval {X:hSet} (S:hsubtype X) (T:WOSubset X) (le : S ⊆ T) :
  LEM -> sub_initial S T le -> T ⊈ S -> ∃ t:T, S ≡ upto t.
Proof.
  set (R := WOrel T).
  assert (min : hasSmallest R).
  { apply (pr2 T). }
  intros lem ini ne.
  set (U := (λ t:T, t ∉ S) : hsubtype (carrier T)). (* complement of S in T *)
  assert (neU : nonempty (carrier U)).
  { apply (squash_to_hProp ne); intros [x [Tx nSx]]. apply hinhpr. exact ((x,,Tx),,nSx). }
  clear ne. assert (minU := min U neU); clear min neU.
  apply (squash_to_hProp minU); clear minU; intros [u [Uu minu]].
  (* minu says that u is the smallest element of T not in S *)
  apply hinhpr. exists u. intro y. split.
  - intro Sy. change (∑ Ty : T y, neg (u ≤ y,, Ty)).
    exists (le y Sy). intro ules. use Uu. exact (ini _ _ _ _ ules).
  - intro yltu. induction yltu as [yinT yltu].
    (* Goal : [S y].  We know y is smaller than the smallest element of T not in S, *)
(*        so at best, constructively, we know [¬ ¬ (S y)].  So prove it by contradiction. *)
    apply (proof_by_contradiction lem).
    intro bc. use yltu. now use minu.
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

(** A choice function provides an element not in each proper subset.  *)

Definition choice_fun (X:hSet) := ∏ S : proper_subtypes_set X, ∑ x : X, ¬ pr1 S x.

Lemma AC_to_choice_fun (X:hSet) : AxiomOfChoice ⇒ ∥ choice_fun X ∥.
Proof.
  intros ac.
  exact (squash_to_hProp (ac (proper_subtypes_set X)
                             (λ S, ∑ x, ¬ (pr1 S x)) pr2)
                         hinhpr).
Defined.

(** Given a choice function, we single out well ordered subsets C of X that
    follow the choice functions advice when constructed by adding one element at
    a time to the top.  We call them "chosen". *)

Definition is_chosen_WOSubset {X:hSet} (g : choice_fun X) (C : WOSubset X) : hProp
  := ∀ c:C, pr1 c = pr1 (g (upto' c)).

Definition Chosen_WOSubset {X:hSet} (g : choice_fun X) := (∑ C, is_chosen_WOSubset g C)%type.

Definition chosenFamily {X:hSet} (g : choice_fun X) : Chosen_WOSubset g -> WOSubset X
  := pr1.

Coercion chosenFamily : Chosen_WOSubset >-> WOSubset.

Lemma chosen_WOSubset_total {X:hSet} (g : choice_fun X) :
  LEM -> is_wosubset_chain (chosenFamily g).
Proof.
  intros lem [C gC] [D gD].
  set (W := max_common_initial C D).
  assert (Q := max_common_initial_is_common_initial C D).
  induction Q as [WC [WD [WCi [WDi WCD]]]]; fold W in WC, WD, WCi, WDi.
  assert (E : W ≡ C ∨ W ≡ D).
  { apply (proof_by_contradiction lem); intro h.
    assert (k := fromnegcoprod_prop h); clear h; induction k as [nc nd].
    assert (nCW : C ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WC.
      - now apply subtype_notEqual_from_negEqual. }
    assert (nDW : D ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WD.
      - now apply subtype_notEqual_from_negEqual. }
    assert (p : ∃ t : C, W ≡ upto t). { now use isInterval. }
    assert (q : ∃ t : D, W ≡ upto t). { now use isInterval. }
    change hfalse.
    apply (squash_to_hProp p); clear p; intros [c cE].
    apply (squash_to_hProp q); clear q; intros [d dE].
    assert (ce : W = upto c).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (de : W = upto d).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (cd := !ce @ de : upto c = upto d).
    assert (cd' : upto' c = upto' d).
    { now apply subtypeEquality_prop. }
    assert (p := gC c); simpl in p.
    assert (q := gD d); simpl in q.
    unfold choice_fun in g.
    assert (cd1 : pr1 c = pr1 d).
    { simple refine (p @ _ @ !q). now induction cd'. }
    clear cd'.
    set (W' := subtype_plus_point W (pr1 c)).
    assert (j := subtype_plus_point_incl W (pr1 c) : W ⊆ W').
    assert (W'c := subtype_plus_point_has_point W (pr1 c) : W' (pr1 c)).
    assert (W'd := transportf W' cd1 W'c : W' (pr1 d)).
    assert (ci : common_initial W' C D).
    { use tpair.
      { abstract (intros x W'x; apply (squash_to_hProp W'x); intros [Wx|e];
                  [ exact (WC x Wx) | induction e; exact (pr2 c) ]) using L. }
      use tpair.
      { abstract (intros x W'x; apply (squash_to_hProp W'x); intros [Wx|e];
                  [ exact (WD x Wx) | induction (!cd1 @ e); exact (pr2 d) ]) using M. }
      generalize (L X C D WC c); intro toC; generalize (M X C D WD c d cd1); intro toD.
      change (hProptoType (W' ⊆ C)) in toC.
      change (hProptoType (W' ⊆ D)) in toD.
      assert (cmax : ∏ (v : carrier W') (W'c : W' (pr1 c)),
                     subtype_inc toC v ≤ subtype_inc toC (pr1 c,,W'c)).
      { intros v W'c'. assert (e : c = subtype_inc toC (pr1 c,, W'c')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'c'. induction v as [v W'v]. apply (squash_to_hProp W'v); intros [Wv|k].
        - assert (L := pr1 (cE v) Wv). unfold upto,lt in L.
          assert (Q := @tot_nge_to_le (carrier_set C) (TOrel C) (TOtotal C) _ _ (pr2 L)).
          now apply(h1'' Q).
        - use (TOeq_to_refl C). now apply subtypeEquality_prop. }
      assert (cmax' : ∏ (w : carrier W) (W'c : W' (pr1 c)),
                     subtype_inc toC (subtype_inc j w) < subtype_inc toC (pr1 c,,W'c)).
      { intros w W'c'. assert (e : c = subtype_inc toC (pr1 c,, W'c')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'c'. induction w as [v Wv].
        assert (L := pr1 (cE v) Wv). unfold upto,lt in L.
        assert (Q := @tot_nge_to_le (carrier_set C) (TOrel C) (TOtotal C) _ _ (pr2 L)).
        apply (@tot_nle_iff_gt (carrier_set C) (TOrel C) (pr122 C)).
        split.
        - now apply (h1'' Q).
        - intros e. assert (e' := maponpaths pr1 e); clear e. change (v = pr1 c)%type in e'.
          assert ( L' := pr2 L ). simpl in L'. apply L'; clear L'.
          exact (TOeq_to_refl_1 C c (v,, pr1 L) (!e')). }
      assert (dmax : ∏ (v : carrier W') (W'd : W' (pr1 d)),
                     subtype_inc toD v ≤ subtype_inc toD (pr1 d,,W'd)).
      { intros v W'd'. assert (e : d = subtype_inc toD (pr1 d,, W'd')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'd'. induction v as [v W'v]. apply (squash_to_hProp W'v); intros [Wv|k].
        - assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
          assert (Q := @tot_nge_to_le (carrier_set D) (TOrel D) (TOtotal D) _ _ (pr2 L)).
          now apply(h1'' Q).
        - use (TOeq_to_refl D). apply subtypeEquality_prop. simpl. exact (!k @ cd1). }
      assert (dmax' : ∏ (w : carrier W) (W'd : W' (pr1 d)),
                     subtype_inc toD (subtype_inc j w) < subtype_inc toD (pr1 d,,W'd)).
      { intros w W'd'. assert (e : d = subtype_inc toD (pr1 d,, W'd')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'd'. induction w as [v Wv].
        assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
        assert (Q := @tot_nge_to_le (carrier_set D) (TOrel D) (TOtotal D) _ _ (pr2 L)).
        apply (@tot_nle_iff_gt (carrier_set D) (TOrel D) (pr122 D)).
        split.
        - now apply (h1'' Q).
        - intros e. assert (e' := maponpaths pr1 e); clear e. change (v = pr1 d)%type in e'.
          assert ( L' := pr2 L ). simpl in L'. apply L'; clear L'.
          exact (TOeq_to_refl_1 D d (v,, pr1 L) (!e')). }
      split.
      { intros w' c' W'w' Cc' le.
        apply (squash_to_hProp W'w'); intros B. induction B as [Ww'|e].
        - apply hinhpr, ii1. apply (WCi w' c' Ww' Cc'). now apply (h1'' le).
        - induction e.
          induction (lem (pr1 c = c')) as [e|ne].
          + induction e. exact W'c.
          + use j. rewrite ce. exists Cc'. unfold lt. intro le'. apply ne.
            assert (e : c = (c',,Cc')).
            { apply (TOanti C).
              - exact le'.
              - now apply (h1'' le). }
            exact (maponpaths pr1 e). }
      split.
      { intros w' d' W'w' Dd' le.
        apply (squash_to_hProp W'w'); intros B. induction B as [Ww'|e].
        - apply hinhpr, ii1. apply (WDi w' d' Ww' Dd'). now apply (h1'' le).
        - induction e.
          induction (lem (pr1 d = d')) as [e|ne].
          + induction e. exact W'd.
          + use j. rewrite de. exists Dd'. unfold lt. intro le'. apply ne.
            assert (e : d = (d',,Dd')).
            { apply (TOanti D).
              - exact le'.
              - now apply (h1'' le). }
            exact (maponpaths pr1 e). }
      {
        intros [v W'v] [w W'w]. change (hProptoType (W' v)) in W'v; change (hProptoType (W' w)) in W'w.
        apply (squash_to_hProp W'v); intros [Wv|Ev].
        - apply (squash_to_hProp W'w); intros [Ww|Ew].
          + assert (Q := WCD (v,,Wv) (w,,Ww)).
            change (hProptoType (
                        (subtype_inc WC (v,, Wv) ≤ subtype_inc WC (w,, Ww))
                          ⇔
                          (subtype_inc WD (v,, Wv) ≤ subtype_inc WD (w,, Ww))
                      )%tosubset) in Q.
            assert (e : subtype_inc toC (v,, W'v) = subtype_inc WC (v,, Wv)).
            { now apply subtypeEquality_prop. }
            induction e.
            assert (e : subtype_inc toC (w,, W'w) = subtype_inc WC (w,, Ww)).
            { now apply subtypeEquality_prop. }
            induction e.
            assert (e : subtype_inc toD (v,, W'v) = subtype_inc WD (v,, Wv)).
            { now apply subtypeEquality_prop. }
            induction e.
            assert (e : subtype_inc toD (w,, W'w) = subtype_inc WD (w,, Ww)).
            { now apply subtypeEquality_prop. }
            induction e.
            exact Q.
          + induction Ew. apply logeq_if_both_true.
            * apply cmax.
            * induction (!cd1). apply dmax.
        - induction Ev. apply (squash_to_hProp W'w); intros [Ww|Ew].
          + apply logeq_if_both_false.
            * assert (Q := cmax' (w,,Ww) W'v). unfold lt in Q.
              assert (e : (w,, W'w) = (subtype_inc j (w,, Ww))).
              { now apply subtypeEquality_prop. }
              induction e.
              exact Q.
            * assert (Q := dmax' (w,,Ww) W'd). unfold lt in Q.
              assert (e : (w,, W'w) = (subtype_inc j (w,, Ww))).
              { now apply subtypeEquality_prop. }
              induction e.
              assert (e : subtype_inc toD (pr1 c,, W'v) = subtype_inc toD (pr1 d,, W'd)).
              { now apply subtypeEquality_prop. }
              induction e.
              exact Q.
          + induction Ew. apply logeq_if_both_true ; now use TOeq_to_refl_1. } }
    assert (K := max_common_initial_is_max C D W' ci); fold W in K.
    assert (Wc : W (pr1 c)).
    { exact (K (pr1 c) W'c). }
    assert (L := pr1 (cE (pr1 c)) Wc). induction L as [Cc Q]. change (neg (c ≤ pr1 c,, Cc)) in Q.
    apply Q; clear Q.
    assert (Y : c = pr1 c,, Cc).
    { now apply subtypeEquality_prop. }
    induction Y. exact (TOrefl C c). }
  change (wosub_comparable C D). unfold wosub_comparable.
  apply (squash_to_hProp E); clear E; intros E. apply hinhpr.
  Set Printing Coercions.
  induction E as [eWC|eWD].
  - apply ii1.
    assert (e : W = C).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WD. }
    split.
    { intros x y le. apply (pr1 (WCD x y)). now apply (h1'' le). }
    exact WDi.
  - apply ii2.
    assert (e : W = D).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WC. }
    split.
    { intros x y le. apply (pr2 (WCD x y)). now apply (h1'' le). }
    exact WCi.
  Unset Printing Coercions.
Defined.

Theorem ZermeloWellOrdering {X:hSet} : AxiomOfChoice ⇒ ∃ R : hrel X, isWellOrder R.
(* see http://www.math.illinois.edu/~dan/ShortProofs/WellOrdering.pdf *)
Proof.
  intros ac. assert (lem := AC_to_LEM ac).
  (* a choice function g allows us to single out the "chosen" well ordered subsets of X *)
  apply (squash_to_hProp (AC_to_choice_fun X ac)); intro g.
  set (S := chosenFamily g).
  set (Schain := chosen_WOSubset_total g lem).
  (* we form the union, W, of all the chosen (well ordered) subsets of X *)
  set (W := ⋃ Schain).
  (* we show W itself is chosen, so W is the biggest chosen subset of X *)
  assert (Wchosen : is_chosen_WOSubset g W).
  { intros [w Ww]. apply (squash_to_hProp Ww); intros [C Cw].
    change (hProptoType (C w)) in Cw. simpl.
    assert (Q := pr2 C (w,,Cw)); simpl in Q.
    simple refine (Q @ _); clear Q.
    assert (Q := chain_union_le S Schain C : C ≼ W).
    assert (e : upto ((w,,Cw):C) = upto ((w,,Ww):W)).
    { now apply upto_eqn. }
    assert (e' : upto' ((w,,Cw):C) = upto' ((w,,Ww):W)).
    { now apply subtypeEquality_prop. }
    clear e.
    change (pr1 (g (upto' ((w,, Cw):C))) = pr1 (g (upto' ((w,, Ww):W)))).
    induction e'.
    reflexivity. }
  (* now we prove W is all of X *)
  assert (all : ∀ x, W x).
  { (* ... for if not, we can add a chosen element and get a bigger chosen subset *)
    apply (proof_by_contradiction lem); intro n.
    (* it's not constructive to get an element not in W: *)
    assert (Q := negforall_to_existsneg _ lem n); clear n.
    change hfalse.
    induction W as [W wo].
    change (hProptoType (∃ x : X, ¬ W x)) in Q.
    (* xn is the chosen element not in W: *)
    set (xnW := g (W,,Q) : ∑ x : X, ¬ W x).
    set (x := pr1 xnW).



    assert (Wx : W x).
    {


      admit. }
    exact (pr2 xnW Wx). }
  clear Wchosen.
  apply hinhpr.
  induction W as [W R'].
  change (∏ x : X, W x)%type in all.
  change (WellOrdering X).
  assert (e : X = carrier_set W).
  { apply (invmap (hSet_univalence _ _)). apply invweq. apply weqpr1.
    intros x.
    simpl in all.
    apply iscontraprop1.
    - apply propproperty.
    - apply all. }
  induction e. exact R'.
Admitted.
