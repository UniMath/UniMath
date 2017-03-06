(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.OrderedSets.
Local Open Scope poset.
Local Open Scope subtype.
Local Open Scope logic.

Definition SubsetWithWellOrdering (X:hSet) :=
  (∑ (S:hsubtype X) (R : hrel (carrier_set S)), isWellOrder R).

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


Abort.


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


Abort.


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
    apply (decidable_proof_by_contradiction (dec _)).
    intro bc. apply yltu. apply minu. exact bc.
Defined.

Lemma chain_union {X:hSet} {I:UU} (S : I -> SubsetWithWellOrdering X) :
  (∏ (i j:I), ((S i ≼ S j) ∨ (S j ≼ S i))) ->
  ∑ (R : hrel (carrier_set (subtype_union S))) (h : isWellOrder R),
  ∏ i, S i ≼ (subtype_union S ,, (R ,, h)).
Proof.
  intro chain.
  use tpair.
  - intros x y.
    induction x as [x a], y as [y b].
    simple refine (squash_to_set isasethProp _ _ a).
    + intro a'; clear a.
      induction a' as [i p].
      set (s := (x,,p) : S i).
      simple refine (squash_to_set isasethProp _ _ b).
      * intro b'; clear b.
        induction b' as [j q].
        set (t := (y,,q) : S j).
        assert (ch := chain i j); clear chain.
        simple refine (squash_to_set isasethProp _ _ ch).
        -- clear ch; intro ch. induction ch as [ilej|jlei].
           ++ set (s' := subtype_inc (pr1 ilej) s).
              exact (s' ≤ t).
           ++ set (t' := subtype_inc (pr1 jlei) t).
              exact (s ≤ t').
        -- clear ch; intros ch ch'; simpl.
           induction ch as [ch|ch], ch' as [ch'|ch'].
           ++ simpl. apply (maponpaths (λ ch, subtype_inc (pr1 ch) s ≤ t)).
              change (ch = ch'). apply propproperty.
           ++ simpl.

Abort.
