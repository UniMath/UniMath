(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.OrderedSets.
Local Open Scope poset.
Local Open Scope subtype.
Local Open Scope logic.

Definition SubsetWithWellOrdering (X:hSet) :=
  (∑ (S:hsubtype X) (R : hrel S), isWellOrder R)%type.

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
  intro l.
  unfold SubsetWithWellOrdering,isWellOrder,isTotalOrder in S.
  apply (squash_to_prop (pr2122 S s s')).
  { apply propproperty. }
  change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
  intro c. induction c as [c|c].
  - exact c.
  - induction le as [le b].
    assert (k := b s' s c).
    unfold SubsetWithWellOrdering,isWellOrder,isTotalOrder,istotal,isPartialOrder in T.
    assert (k' := pr21122 T _ _ l k); clear k. simpl in k'.
    assert (p : s = s').
    { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
    induction p.
    unfold isPartialOrder,ispreorder in S.
    exact (pr211122 S _).
Defined.

Definition isclosed_UU {X:hSet} (S T:SubsetWithWellOrdering X) : UU
  := ∑ (le : S ⊑ T), ∀ (s:S) (t:T), t ≤ inc' le s ⇒ (t ∈ S).

Definition isclosed {X:hSet} (S T:SubsetWithWellOrdering X) : hProp
  := hProppair (isclosed_UU S T) (propproperty _ ).

  (* := ∑ (le : S ⊑ T), ∀ (s:S) (t:T), t ≤ inc' le s ⇒ (t ∈ S). *)

Notation "S ≼ T" := (isclosed S T) (at level 95) : wosubset.

Definition isclosed_smaller {X:hSet} (S T:SubsetWithWellOrdering X) : hProp := (S ≼ T) ∧ (∃ t:T, t ∉ S).

Notation "S ≺ T" := (isclosed_smaller S T) (at level 95) : wosubset.

(* [upto s x] means x is in S and, as an element of S, it is strictly less than s *)
Definition upto {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : hsubtype X
  := λ x, ∑ h:S x, (x,,h) < s.

Definition upto' {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : hsubtype X
  := λ x, ∑ h:S x, ¬ (s ≤ (x,,h)).

Lemma ord_nge_to_lt {X:hSet} (S : SubsetWithWellOrdering X) (x y:S) :
  ¬ (x ≤ y) <-> y < x.
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
  { intros yltx xley. induction yltx as [ylex neq].
    apply neq; clear neq.
    now apply anti. }
Defined.

Lemma upto'_eq_upto {X:hSet} {S:SubsetWithWellOrdering X} (s:S) : upto' s ≡ upto s.
Proof.
  apply subtype_equal_cond. split.
  { intros x. simpl in x. induction x as [x nle]. induction nle as [xinS nle]. simpl.
    exists xinS. exact (pr1 (ord_nge_to_lt _ _ _) nle). }
  { intro x. induction x as [x lt]. induction lt as [xinS lt]. induction lt as [le ne].
    simpl. exists xinS. intro le'. assert (anti := pr21122 S); simpl in anti.
    assert (anti' := anti s (x,,xinS) le' le); clear le' anti.
    apply ne, pathsinv0, anti'. }
Defined.

Local Open Scope prop.

Definition isInterval {X:hSet} (S T:SubsetWithWellOrdering X) : LEM -> S ≺ T -> ∑ t:T, S ≡ upto t.
Proof.
  set (R := rel T). intros lem lt.
  unfold isclosed_smaller in lt. induction lt as [le ne].
  assert (min := pr222 T); simpl in min; fold R in min.
  unfold mincondition in min.
  set (U := (λ t:T, t ∉ S) : hsubtype T).
  assert (ne' : nonempty U).
  { simple refine (hinhuniv _ ne); intro u. apply hinhpr. exact u. }
  clear ne. assert (minU := min U ne'); clear min ne'.
  induction minU as [u minu]. fold (SubsetWithWellOrdering_to_subtype T) in u.
  induction minu as [uinU minu].
  (* minu says that u is the smallest element of T not in S *)
  exists u. intro y. split.
  - intro yinS. set (s := (y ,, yinS) : S). set (s' := subtype_inc (pr11 le) s).
    unfold upto. exists (pr2 s'). set (y' := y ,, pr2 s'). apply ord_nge_to_lt. intro ules.
    assert (q := pr2 le s u ules); clear ules.
    apply uinU. exact q.
  - intro yltu. induction yltu as [yinT yltu].
    apply (dneg_LEM _ lem).     (* we prove that y is in S by contradiction *)
    intro bc.
    assert (nuley := pr2 (ord_nge_to_lt _ _ _) yltu). apply nuley; clear nuley.
    exact (minu (y,,yinT) bc).
Defined.
