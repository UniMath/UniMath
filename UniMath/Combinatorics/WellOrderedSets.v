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

Local Definition lt {X:hSet} {S : SubsetWithWellOrdering X} (s s' : S) := (s ≤ s') ∧ ¬ (s = s').

Notation "s < s'" := (lt s s') : wosubset.

Open Scope logic.

Open Scope prop.

Definition subposet {X:hSet} (S T:SubsetWithWellOrdering X) : hProp
  := ∑ (le : S ⊆ T), ∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s'.

Notation " S ⊑ T " := (subposet S T) (at level 95) : wosubset.

Notation " S ⊏ T " := ((S ⊑ T) ∧ (T ⊈ S)) (at level 95) : wosubset.

Definition subposet_to_subtype {X:hSet} {S T:SubsetWithWellOrdering X} : S ⊑ T -> S ⊆ T
  := pr1.

Local Definition inc' {X} {S T : SubsetWithWellOrdering X} : (S ⊑ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (subposet_to_subtype le) s).
Defined.

Definition subposet_reflect {X:hSet} {S T:SubsetWithWellOrdering X} (le : S ⊑ T)
      (s s' : S) : inc' le s ≤ inc' le s' -> s ≤ s'.
Proof.
  intro l. apply (squash_to_prop (pr2122 S s s')).
  { apply propproperty. }
  change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
  intro c. induction c as [c|c].
  - exact c.
  - induction le as [le b].
    assert (k := b s' s c).
    assert (k' := pr21122 T _ _ l k); clear k. simpl in k'.
    assert (p : s = s').
    { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
    induction p.
    exact (pr211122 S _).
Defined.

Definition isclosed_UU {X:hSet} (S T:SubsetWithWellOrdering X) : UU
  := ∑ (le : S ⊑ T), ∀ (s:S) (t:T), t ≤ inc' le s ⇒ (t ∈ S).

Definition isclosed (X:hSet) : hrel (SubsetWithWellOrdering X)
  := λ S T, hProppair (isclosed_UU S T) (propproperty _ ).

  (* := ∑ (le : S ⊑ T), ∀ (s:S) (t:T), t ≤ inc' le s ⇒ (t ∈ S). *)

Notation "S ≼ T" := (isclosed _ S T) (at level 95) : wosubset.

Lemma isclosed_isrefl {X:hSet} : isrefl (isclosed X).
Proof.
  intro S.
  use tpair.
  - use tpair.
    + intros x s. exact s.
    + abstract (intros s t le; now induction s, t).
  - intros s t le. exact (pr2 t).
Defined.

Definition isclosed_smaller {X:hSet} (S T:SubsetWithWellOrdering X) : hProp := (S ≼ T) ∧ (∃ t:T, t ∉ S).

Notation "S ≺ T" := (isclosed_smaller S T) (at level 95) : wosubset.

(* [upto s x] means x is in S and, as an element of S, it is strictly less than s *)
Definition upto {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : hsubtype X
  := λ x, ∑ h:S x, (x,,h) < s.

Lemma ord_nge_iff_lt {X:hSet} (S : SubsetWithWellOrdering X) (x y:S) :
  ¬ (x ≤ y) <-> y < x.
(* this is actually a fact about total orderings and could be moved upstream *)
Proof.
  assert (tot := pr2122 S); simpl in tot.
  assert (refl := pr211122 S); simpl in refl.
  assert (anti := pr21122 S); simpl in anti.
  split.
  { intros nle. split.
    - assert (q := tot x y). simple refine (hinhuniv _ q); intro q'; clear q.
      induction q' as [Rxy|Ryx].
      + apply fromempty, nle, Rxy.
      + exact Ryx.
    - intros ne. induction ne. apply nle; clear nle. exact (refl y). }
  { intros yltx xley. induction yltx as [ylex neq]. apply neq; clear neq. now apply anti. }
Defined.

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
  - intro yinS. set (s := (y ,, yinS) : S). set (s' := subtype_inc (pr11 le) s).
    exists (pr2 s'). set (y' := y ,, pr2 s'). apply ord_nge_iff_lt. intro ules.
    assert (q := pr2 le s u ules); clear ules.
    apply uinU. exact q.
  - intro yltu. induction yltu as [yinT yltu].
    apply decidable_proof_by_contradiction.
    { apply dec. }
    intro bc.
    assert (nuley := pr2 (ord_nge_iff_lt _ _ _) yltu). apply nuley; clear nuley.
    exact (minu (y,,yinT) bc).
Defined.

Lemma chain_union {X:hSet} {I:UU} (S : I -> SubsetWithWellOrdering X) :
  (∏ (i j:I), ((S i ≼ S j) ∨ (S j ≼ S i))) ->
  ∑ (R : hrel (carrier_set (subtype_union S)))
    (h : isWellOrder R),
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
           ++ set (s' := inc' (pr1 ilej) s).
              exact (s' ≤ t).
           ++ set (t' := inc' (pr1 jlei) t).
              exact (s ≤ t').
        -- clear ch; intros ch ch'; simpl.
           induction ch as [ch|ch], ch' as [ch'|ch'].
           ++ simpl. apply (maponpaths (λ ch, inc' (pr1 ch) s ≤ t)).
              change (ch = ch'). apply propproperty.
           ++ simpl.

Abort.