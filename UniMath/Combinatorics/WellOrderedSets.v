(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.OrderedSets.
Local Open Scope poset.
Local Open Scope subtype.
Local Open Scope logic.
Local Open Scope set.

Definition SubsetWithWellOrdering_set (X:hSet) : hSet
  := ∑ (S:subtype_set X) (R : hrel_set (carrier_set S)), isWellOrder R.

Definition SubsetWithWellOrdering (X:hSet) : UU := SubsetWithWellOrdering_set X.

Definition SubsetWithWellOrdering_to_subtype {X:hSet} : SubsetWithWellOrdering X -> hsubtype X
  := pr1.

Coercion SubsetWithWellOrdering_to_subtype : SubsetWithWellOrdering >-> hsubtype.

Local Definition rel {X:hSet} (S : SubsetWithWellOrdering X) : hrel S := pr12 S.

Delimit Scope wosubset with wosubset. (* subsets equipped with a well ordering *)

Open Scope wosubset.

Delimit Scope wosubset with wosubset.

Notation "s ≤ s'" := (rel _ s s') : wosubset.

(* Coercion rel : SubsetWithWellOrdering >-> hrel. *)

Local Definition lt {X:hSet} {S : SubsetWithWellOrdering X} (s s' : S) := ¬ (s' ≤ s).

Notation "s < s'" := (lt s s') : wosubset.

Open Scope logic.

Open Scope prop.

Definition wosub_le (X:hSet) : hrel (SubsetWithWellOrdering X)
  := λ S T, ∑ (le : S ⊆ T),
     (∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s')
     ∧
     (∀ (s:S) (t:T), t ≤ subtype_inc le s ⇒ (t ∈ S)).

Notation "S ≼ T" := (wosub_le _ S T) (at level 70) : wosubset.

Definition wosub_equal (X:hSet) : hrel (SubsetWithWellOrdering X) := λ S T, (S ≼ T) ∧ (T ≼ S).

Notation "S ≣ T" := (wosub_equal _ S T) (at level 70) : wosubset.

Theorem wosub_univalence {X:hSet} (S T : SubsetWithWellOrdering X) : (S = T) ≃ (S ≣ T).
Proof.
  intros. unfold wosub_equal.
  intermediate_weq (∑ (le : S ⊆ T), ∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s').
  - admit.
  -


Admitted.

Definition wosub_inc {X} {S T : SubsetWithWellOrdering X} : (S ≼ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (pr1 le) s).
Defined.

Definition wosub_fidelity {X:hSet} {S T:SubsetWithWellOrdering X} (le : S ≼ T)
      (s s' : S) : s ≤ s' <-> wosub_inc le s ≤ wosub_inc le s'.
Proof.
  split.
  { intro l. exact (pr12 le s s' l). }
  { intro l. apply (squash_to_prop (pr2122 S s s')).
    { apply propproperty. }
    change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
    intro c. induction c as [c|c].
    - exact c.
    - induction le as [le b].  induction b as [b b'].
      assert (k := b s' s c).
      assert (k' := pr21122 T _ _ l k); clear k. simpl in k'.
      assert (p : s = s').
      { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
      induction p. exact (pr211122 S _). }
Defined.

Local Lemma h1 {X} {S:SubsetWithWellOrdering X} {s t u:S} : s = t -> t ≤ u -> s ≤ u.
Proof.
  intros p le. induction p. exact le.
Defined.

Local Lemma h1' {X} {S:SubsetWithWellOrdering X} {s t u:S} : s = t -> u ≤ s -> u ≤ t.
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
    + intros s u l.
      change (hProptoType (u ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) s))) in l.
      set (uinT := pr1 u,,pr22 j (subtype_inc (pr1 i) s) u l : T).
      assert (p : subtype_inc (pr1 j) uinT = u).
      { now apply subtypeEquality_prop. }
      assert (q := h1 p l : subtype_inc (pr1 j) uinT ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) s)).
      assert (r := pr2 (wosub_fidelity j _ _) q).
      assert (b := pr22 i _ _ r); simpl in b.
      exact b.
  - intros S.
    use tpair.
    + intros x xinS. exact xinS.
    + split.
      * intros s s' le. induction s, s'; exact le.
      * intros s s' le. exact (pr2 s').
  - intros S T i j.
    induction i as [i i'], i' as [i' i''].
    induction j as [j j'], j' as [j' j''].
    assert (q := pr2 (subtype_containment_isPartialOrder X) S T i j); simpl in q.
    unfold SubsetWithWellOrdering_to_subtype in q.


Admitted.

Definition WosubPoset (X:hSet) : Poset.
Proof.
  exists (SubsetWithWellOrdering_set X).
  exists (λ S T, S ≼ T).
  exact (wosub_le_isPartialOrder X).
Defined.

Definition wosub_le_smaller {X:hSet} (S T:SubsetWithWellOrdering X) : hProp := (S ≼ T) ∧ (∃ t:T, t ∉ S).

Notation "S ≺ T" := (wosub_le_smaller S T) (at level 70) : wosubset.

(* [upto s x] means x is in S and, as an element of S, it is strictly less than s *)
Definition upto {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : hsubtype X
  := λ x, ∑ h:S x, (x,,h) < s.

Local Open Scope prop.

Definition isInterval {X:hSet} (S T:SubsetWithWellOrdering X) :
  subtype_decidable S -> S ≺ T -> ∑ t:T, S ≡ upto t.
Proof.
  set (R := rel T). intros dec lt.
  induction lt as [le ne].
  assert (min := pr222 T); simpl in min; fold R in min.
  set (U := (λ t:T, t ∉ S) : hsubtype T).
  assert (ne' : nonempty U).
  { simple refine (hinhuniv _ ne); intro u. apply hinhpr. exact u. }
  clear ne. assert (minU := min U ne'); clear min ne'.
  induction minU as [u minu]. fold (SubsetWithWellOrdering_to_subtype T) in u.
  induction minu as [uinU minu].
  (* minu says that u is the smallest element of T not in S *)
  exists u. intro y. split.
  - intro yinS. set (s := (y ,, yinS) : S). set (s' := subtype_inc (pr1 le) s).
    exists (pr2 s'). set (y' := y ,, pr2 s'). intro ules.
    assert (q := pr22 le s u ules); clear ules.
    apply uinU. exact q.
  - intro yltu. induction yltu as [yinT yltu].
    (* Goal : [S y].  We know y is smaller than the smallest element of T not in S,
       so at best, constructively, we know [¬ ¬ (S y)].  So prove it by contradiction. *)
    apply (decidable_proof_by_contradiction (dec _)).
    intro bc. apply yltu. apply minu. exact bc.
Defined.

Definition chain_union_prelim_prop {X:hSet} {S T:SubsetWithWellOrdering X}
           (x:S) (y:T) (ch : (S ≼ T) ⨿ (T ≼ S)) : hProp.
Proof.
  induction ch as [i|j].
  + exact (subtype_inc (pr1 i) x ≤ y).
  + exact (x ≤ subtype_inc (pr1 j) y).
Defined.

Definition isconst {X Y:UU} (f : X -> Y) := (∏ x x', f x = f x')%type.

Lemma chain_union_prelim_eq {X:hSet} {S T:SubsetWithWellOrdering X}
      (s:S) (t:T) : isconst (chain_union_prelim_prop s t).
Proof.
  intros ch ch'. induction ch as [ch|ch], ch' as [ch'|ch'].
  + apply (maponpaths (λ ch : S ≼ T, subtype_inc (pr1 ch) s ≤ t)). apply propproperty.
  + apply (invmap (weqlogeq _ _)). split.
    * intros slet. simple refine (h1 _ (pr12 ch' _ _ slet)).
      now apply subtypeEquality_prop.
    * intros tles. simple refine (h1' _ (pr12 ch _ _ tles)).
      now apply subtypeEquality_prop.
  + apply (invmap (weqlogeq _ _)). split.
    * intros slet. simple refine (h1' _ (pr12 ch' _ _ slet)).
      now apply subtypeEquality_prop.
    * intros slet. simple refine (h1 _ (pr12 ch _ _ slet)).
      now apply subtypeEquality_prop.
  + apply maponpaths, maponpaths. apply propproperty.
Defined.

Definition chain_union_prelim {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i)
           (x y : carrier_set (⋃ (λ x : I, S x)))
           (a : ∑ i : I, (λ x : I, S x) i (pr1 x))
           (b : ∑ i : I, (λ x : I, S x) i (pr1 y)) : hProp.
Proof.
  assert (ch := chain (pr1 a) (pr1 b)); clear chain.
  simple refine (squash_to_set isasethProp _ _ ch).
  -- exact (chain_union_prelim_prop (pr1 x,,pr2 a) (pr1 y,,pr2 b)).
  -- exact (chain_union_prelim_eq   (pr1 x,,pr2 a) (pr1 y,,pr2 b)).
Defined.

Definition chain_union_prelim_eq2 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) x y a :
  isconst (chain_union_prelim chain x y a).
Proof.
  intros b b'.
Admitted.

Definition chain_union_prelim2 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i)
           (x y : carrier_set (⋃ (λ x : I, S x))) :
  (∑ i : I, (λ x0 : I, S x0) i (pr1 x)) → hProp.
Proof.
  intro a.
  simple refine (squash_to_set isasethProp _ _ (pr2 y)). (* y ∈ S j, for some j *)
  * exact (chain_union_prelim     chain x y a).
  * exact (chain_union_prelim_eq2 chain x y a).
Defined.

Definition chain_union_prelim2_eqn {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) x y :
  isconst (chain_union_prelim2 chain x y).
Proof.
  intros a a'.
Admitted.

Definition chain_union_rel {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) :
  hrel (carrier_set (⋃ (λ x : I, S x))).
Proof.
  intros x y.                 (* now define [x ≤ y] on the union *)
  simple refine (squash_to_set isasethProp _ _ (pr2 x)). (* x ∈ S i, for some i *)
  + exact (chain_union_prelim2     chain x y).
  + exact (chain_union_prelim2_eqn chain x y).
Defined.

Lemma chain_union {X:hSet} {I:UU} (S : I -> SubsetWithWellOrdering X) :
  (∀ (i j:I), ((S i ≼ S j) ∨ (S j ≼ S i))) ->
  ∑ (R : hrel (carrier_set (subtype_union S))) (h : isWellOrder R),
  ∀ i, S i ≼ (subtype_union S ,, (R ,, h)).
Proof.
  intro chain.
  exists (chain_union_rel chain).
  use tpair.
  - repeat split.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - intros i.
    use tpair.
    + intros x s. change (∃ j, S j x). admit.
    + split.
      * intros s s' j. admit.
      * intros s t j. admit.
Admitted.
