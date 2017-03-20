(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.OrderedSets.

Definition mincondition {X : UU} (R : hrel X) : UU
  := ∏ S : hsubtype X, (∃ s, S s) -> ∑ s:X, S s × ∏ t:X, S t -> R s t.

Lemma iswellordering_istotal {X : UU} (R : hrel X) : mincondition R -> istotal R.
Proof.
  intros iswell x y.
  (* make the doubleton subset containing x and y *)
  set (S := (λ z, ∥ (z=x) ⨿ (z=y) ∥)).
  assert (x' := hinhpr (ii1 (idpath _)) : S x).
  assert (y' := hinhpr (ii2 (idpath _)) : S y).
  assert (h : ∃ s, S s).
  { apply hinhpr. exists x. exact x'. }
  assert (q := iswell S h); clear h iswell.
  induction q as [s min], min as [h issmallest].
  apply (squash_to_prop h).
  { apply propproperty. }
  clear h. intro d. apply hinhpr. induction d as [d|d].
  - induction (!d); clear d. now apply ii1, issmallest.
  - induction (!d); clear d. now apply ii2, issmallest.
Defined.

Local Open Scope poset.
Local Open Scope subtype.
Local Open Scope logic.
Local Open Scope set.

Lemma isaprop_mincondition {X : hSet} (R : hrel X) : isantisymm R -> isaprop (mincondition R).
Proof.
  intros antisymm.
  apply isaprop_assume_it_is; intro min.
  assert (istot := iswellordering_istotal R min).
  apply impred. intro S. apply impred. intros _.
  apply invproofirrelevance. intros s t.
  apply subtypeEquality.
  * intros x. apply isapropdirprod.
    + apply propproperty.
    + apply impred; intro y. apply impred; intros _. apply propproperty.
  * induction s as [x i], t as [y j], i as [I i], j as [J j]; simpl.
    apply (squash_to_prop (istot x y)).
    { apply setproperty. }
    intro c. induction c as [c|c].
    - apply antisymm.
      + exact c.
      + now apply j.
    - apply antisymm.
      + now apply i.
      + exact c.
Defined.

Definition isWellOrder {X : hSet} (R : hrel X) : hProp.
Proof.
  exists (isTotalOrder R × mincondition R)%type.
  apply isaprop_assume_it_is; intro iswell.
  induction iswell as [istot hasmin].
  induction istot as [ispo istot].
  unwrap_isPartialOrder ispo.
  apply isapropdirprod.
  { exact (isaprop_isTotalOrder R). }
  now apply isaprop_mincondition.
Defined.

Definition WellOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isWellOrder R.

Definition SubsetWithWellOrdering_set (X:hSet) : hSet
  := ∑ (S:subtype_set X), WellOrdering (carrier_set S).

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

Definition wosub_le0 (S:hSet) : hrel (WellOrdering S)
  := λ R R', ∀ s s' : S, pr1 R s s' ⇒ pr1 R' s s'.

Lemma wosub_le0_eq (S:hSet) R R' : wosub_le0 S R R' -> R = R'.
Proof.
  intros le. simple refine (invmap (total2_paths_equiv _ _ _) _).
  induction R as [R w], R' as [R' w'].
  change (∏ s s' : S, R s s' -> R' s s')%type in le.
  use tpair.
  - change (R=R'). apply funextfun; intro s; apply funextfun; intro s'.
    apply (invmap (weqlogeq _ _)). split.
    { exact (le s s'). }
    apply (squash_to_prop (pr21 w s s')). (* istotal *)
    { apply propproperty. }
    intro r. induction r as [a|b].
    { intros _. exact a. }
    { intros c. assert (p : s = s').
      { apply w'.
        - exact c.
        - apply le. exact b. }
      induction p.
      apply w. }
  - apply propproperty.
Defined.

Definition wosub_le (X:hSet) : hrel (SubsetWithWellOrdering X)
  := λ S T, ∑ (le : S ⊆ T),
     (∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s')
     ∧
     (∀ (s:S) (t:T), t ≤ subtype_inc le s ⇒ (t ∈ S)).

Notation "S ≼ T" := (wosub_le _ S T) (at level 70) : wosubset.

Lemma wosub_le_isrefl {X:hSet} : isrefl (wosub_le X).
Proof.
  intros S.
  use tpair.
  + intros x xinS. exact xinS.
  + split.
    * intros s s' le. induction s, s'; exact le.
    * intros s s' le. exact (pr2 s').
Defined.

Lemma wosub_le_eq (X:hSet) (S:hsubtype X) (R R':WellOrdering (carrier_set S)) :
  (S,,R) ≼ (S,,R') <-> R = R'.
Proof.
  split.
  { intros le. apply wosub_le0_eq. intros s s' r.
    unfold wosub_le in le; simpl in le.
    induction le as [le a], a as [a b].
    assert (q := a s s' r).
    unfold rel in q; simpl in q.
    assert (E : le = λ _, idfun _).
    { apply funextsec; intro x; apply funextsec; intro w. apply propproperty. }
    assert (F : ∏ s, s = subtype_inc le s).
    { intro t. induction (!E). apply subtypeEquality_prop. reflexivity. }
    induction (F s).
    induction (F s').
    exact q. }
  { intro E. induction E. apply wosub_le_isrefl. }
Defined.

Definition wosub_equal (X:hSet) : hrel (SubsetWithWellOrdering X) := λ S T, (S ≼ T) ∧ (T ≼ S).

Notation "S ≣ T" := (wosub_equal _ S T) (at level 70) : wosubset.

Open Scope subtype.

Definition wosub_univalence_map {X:hSet} (S T : SubsetWithWellOrdering X) : (S = T) -> (S ≣ T).
Proof.
  intros e. induction e. unfold wosub_equal.
  simple refine ((λ L, dirprodpair L L) _).
  use tpair.
  + intros x s. exact s.
  + split.
    * intros s s' le. exact le.
    * intros s t le. apply t.
Defined.

Theorem wosub_univalence {X:hSet} (S T : SubsetWithWellOrdering X) : (S = T) ≃ (S ≣ T).
Proof.
  simple refine (remakeweq _).
  { unfold wosub_equal.
    intermediate_weq (S ╝ T).
    - apply total2_paths_equiv.
    - intermediate_weq (∑ e : S ≡ T, S ≼ T ∧ T ≼ S).
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
                { intros s t le. simpl in t. simpl. exact (pr2 t). } } }
            { use tpair.
              { intros s. change (S s → S s). exact (idfun _). }
              { split.
                { intros s s' le. exact le. }
                { intros s t le. simpl in t. simpl. exact (pr2 t). } } } }
          { simpl. unfold rel. simpl. intros [[a [b _]] [d [e _]]].
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

Lemma wosub_univalence_compute {X:hSet} (S T : SubsetWithWellOrdering X) (e : S = T) :
  wosub_univalence S T e = wosub_univalence_map S T e.
Proof.
  reflexivity.
Defined.

Definition wosub_inc {X} {S T : SubsetWithWellOrdering X} : (S ≼ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (pr1 le) s).
Defined.

Definition wosub_fidelity {X:hSet} {S T:SubsetWithWellOrdering X} (le : S ≼ T)
      (s s' : S) : s ≤ s' <-> wosub_inc le s ≤ wosub_inc le s'.
Proof.
  set (Srel := pr12 S).
  assert (Stot : istotal Srel).
  { apply (pr2 S). }
  set (Trel := pr12 T).
  assert (Tanti : isantisymm Trel).
  { apply (pr2 T). }
  split.
  { intro l. exact (pr12 le s s' l). }
  { intro l. apply (squash_to_prop (Stot s s')).
    { apply propproperty. }
    change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
    intro c. induction c as [c|c].
    - exact c.
    - induction le as [le b].  induction b as [b b'].
      assert (k := b s' s c).
      assert (k' := Tanti _ _ l k); clear k. simpl in k'.
      assert (p : s = s').
      { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
      induction p. apply (pr2 S). }
Defined.

Local Lemma h1 {X} {S:SubsetWithWellOrdering X} {s t u:S} : s = t -> t ≤ u -> s ≤ u.
Proof.
  intros p le. induction p. exact le.
Defined.

Local Lemma h1' {X} {S:SubsetWithWellOrdering X} {s t u:S} : s = t -> u ≤ s -> u ≤ t.
Proof.
  intros p le. induction p. exact le.
Defined.

Local Lemma h1'' {X} {S:SubsetWithWellOrdering X} {r s t u:S} : r ≤ t -> pr1 r = pr1 s -> pr1 t = pr1 u -> s ≤ u.
Proof.
  intros le p q.
  assert (p' : r = s).
  { now apply subtypeEquality_prop. }
  assert (q' : t = u).
  { now apply subtypeEquality_prop. }
  induction p', q'. exact le.
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
  - apply wosub_le_isrefl.
  - intros S T i j. apply (invmap (wosub_univalence _ _)). exact (i,,j).
Defined.

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
  isDecidablePredicate S -> S ≺ T -> ∑ t:T, S ≡ upto t.
Proof.
  set (R := rel T).
  assert (min : mincondition R).
  { apply (pr2 T). }
  intros dec lt.
  induction lt as [le ne].
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
    simple refine (uinU _). exact q.
  - intro yltu. induction yltu as [yinT yltu].
    (* Goal : [S y].  We know y is smaller than the smallest element of T not in S,
       so at best, constructively, we know [¬ ¬ (S y)].  So prove it by contradiction. *)
    apply (decidable_proof_by_contradiction (dec _)).
    intro bc. simple refine (yltu _). apply minu. exact bc.
Defined.

(** Our goal now is to equip the union of a chain of subsets-with-well-orderings
    with a well ordering. *)

Lemma chain_union_prelim_eq0 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i)
           (x y : X) (i j: I) (xi : S i x) (xj : S j x) (yi : S i y) (yj : S j y) :
  rel (S i) (x ,, xi) (y ,, yi) ⇔ rel (S j) (x ,, xj) (y ,, yj).
Proof.
  simple refine (hinhuniv _ (chain i j)). intros [c|c].
  - split.
    + intro l. assert (q := pr12 c _ _ l); clear l. now apply (h1'' q).
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xi) (y,,yi))). now apply (h1'' l).
  - split.
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xj) (y,,yj))). now apply (h1'' l).
    + intro l. assert (q := pr12 c _ _ l); clear l. now apply (h1'' q).
Defined.

Definition chain_union_prelim_prop {X:hSet} {S T:SubsetWithWellOrdering X}
           (x:S) (y:T) (ch : (S ≼ T) ⨿ (T ≼ S)) : hPropset.
Proof.
  induction ch as [i|j].
  + exact (subtype_inc (pr1 i) x ≤ y).
  + exact (x ≤ subtype_inc (pr1 j) y).
Defined.

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

Lemma chain_ub2 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X} :
  (∀ i j, S i ≼ S j ∨ S j ≼ S i) ->
  (∀ i j, ∃ k, S i ≼ S k ∧ S j ≼ S k).
Proof.
  intros chain i j.
  simple refine (hinhuniv _ (chain i j)); intro c. apply hinhpr. induction c as [ij|ji].
  - exists j. split.
    + exact ij.
    + apply wosub_le_isPartialOrder.
  - exists i. split.
    + apply wosub_le_isPartialOrder.
    + exact ji.
Defined.

Lemma chain_ub3 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X} :
  (∀ i j, S i ≼ S j ∨ S j ≼ S i) ->
  (∀ i j k, ∃ m, S i ≼ S m ∧ S j ≼ S m ∧ S k ≼ S m).
Proof.
  intros chain i j k.
  assert (fil := chain_ub2 chain).
  simple refine (hinhuniv _ (fil i j)). intro n. induction n as [n n'], n' as [ilen jlen].
  simple refine (hinhuniv _ (fil n k)). intro o. induction o as [o o'], o' as [nleo kleo].
  apply hinhpr.
  exists o.
  repeat split.
  - apply (pr11 (wosub_le_isPartialOrder _) _ _ _ ilen nleo).
  - apply (pr11 (wosub_le_isPartialOrder _) _ _ _ jlen nleo).
  - exact kleo.
Defined.

Definition chain_union_prelim {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j, S i ≼ S j ∨ S j ≼ S i)
           (x y:X) (a : ∑ i, S i x) (b : ∑ i, S i y) : hPropset.
Proof.
  assert (ch := chain (pr1 a) (pr1 b)); clear chain.
  simple refine (squash_to_set isasethProp _ _ ch).
  -- exact (chain_union_prelim_prop (x,,pr2 a) (y,,pr2 b)).
  -- exact (chain_union_prelim_eq   (x,,pr2 a) (y,,pr2 b)).
Defined.

Lemma squash_to_set_eqn {X Y : UU} (i : isaset Y) (f : X -> Y)
      (const : ∏ x x', f x = f x') (x : ∥ X ∥) (x' : X) :
  squash_to_set i f const x = f x'.
(* upstream *)
Proof.
  assert (p : hinhpr x' = x).
  - apply propproperty.
  - induction p. reflexivity.
Defined.

Lemma squash_rec {X : UU} (P : ∥ X ∥ -> UU) : (∑ x, P (hinhpr x)) -> (∏ x, P x).
(* upstream, if it turns out to be useful *)
Proof.
  intros xp x.
  assert (q : hinhpr (pr1 xp)  = x).
  - apply propproperty.
  - induction q. exact (pr2 xp).
Defined.

Lemma squash_rec' {X : UU} (P : ∥ X ∥ -> hProp) : (∏ x, P (hinhpr x)) -> (∏ x, P x).
(* upstream *)
Proof.
  intros xp x'.
  simple refine (hinhuniv _ x').
  intro x.
  assert (q : hinhpr x = x').
  { apply propproperty. }
  induction q.
  exact (xp x).
Defined.

Definition pathcomp_set {X : hSet} {a b c : X} : eqset a b -> eqset b c -> eqset a c.
Proof.
  intros p q. induction p. exact q.
Defined.

Ltac intermediate_eqset x := apply (pathcomp_set (b := x)).

Lemma chain_union_prelim_eq1 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i)
           (x y : X) (i j k: I) (xi : S i x) (yj : S j y) (b : S j ≼ S k) :
  (chain_union_prelim chain x y (i,, xi) (j,, yj) = chain_union_prelim chain x y (i,, xi) (k,, pr1 b y yj))%set.
Proof.
  unfold chain_union_prelim. change (chain (pr1 (i,, xi)) (pr1 (j,, yj))) with (chain i j).
  generalize (chain i j). apply squash_rec'. intro c.
  change (chain (pr1 (i,, xi)) (pr1 (k,, pr1 b y yj))) with (chain i k).
  generalize (chain i k). apply squash_rec'. intro d.
  change ((chain_union_prelim_prop (x,, xi) (y,, yj)) c = (chain_union_prelim_prop (x,, xi) (y,, pr1 b y yj)) d).
  induction c as [c|c], d as [d|d].
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
Defined.

Lemma chain_union_prelim_eq2 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) x y a :
  isconst (chain_union_prelim chain x y a).
Proof.
  induction a as [i xi].
  intros [j yj] [k yk].
  unfold chain_union_prelim.
(*   change (  squash_to_set isasethProp (chain_union_prelim_prop (x,, xi) (y,, yj)) *)
(*                           (chain_union_prelim_eq (x,, xi) (y,, yj)) (chain i j) = *)
(*             squash_to_set isasethProp (chain_union_prelim_prop (x,, xi) (y,, yk)) *)
(*                           (chain_union_prelim_eq (x,, xi) (y,, yk)) (chain i k))%set. *)
(*   generalize (chain i j). apply squash_rec'. intros c. *)
(*   generalize (chain i k). apply squash_rec'. intros d. *)
(*   change (chain_union_prelim_prop (x,, xi) (y,,yk) c = chain_union_prelim_prop (x,, xj) (y,, yk) d). *)
(*   induction c as [c|c], d as [d|d]. *)
(*   - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0. *)
(*   - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0. *)
(*   - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0. *)
(*   - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0. *)
(* Defined. *)
Admitted.

Lemma chain_union_prelim_eq3 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) x y b :
  isconst (λ a, chain_union_prelim chain x y a b).
Proof.
  induction b as [k yk].
  intros [i xi] [j xj].
  unfold chain_union_prelim.
  change (chain (pr1 (i,, _)) _) with (chain i k).
  change (chain (pr1 (j,, _)) _) with (chain j k).
  generalize (chain i k). apply squash_rec'. intros c.
  generalize (chain j k). apply squash_rec'. intros d.
  change (chain_union_prelim_prop (x,, xi) (y,,yk) c = chain_union_prelim_prop (x,, xj) (y,, yk) d).
  induction c as [c|c], d as [d|d].
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
  - unfold chain_union_prelim_prop,subtype_inc;simpl. apply weqlogeq. now apply chain_union_prelim_eq0.
Defined.

Definition chain_union_prelim2 {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i)
           (x:X) (y : carrier_set (⋃ (λ x : I, S x))) :
  (∑ i : I, S i x) → hPropset.
Proof.
  intro a.
  simple refine (squash_to_set isasethProp _ _ (pr2 y)). (* y ∈ S j, for some j *)
  * exact (chain_union_prelim     chain x (pr1 y) a).
  * exact (chain_union_prelim_eq2 chain x (pr1 y) a).
Defined.

Definition chain_union_prelim2_eqn {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) x y :
  isconst (chain_union_prelim2 chain x y).
Proof.
  intros a a'.
  induction y as [y u]. generalize u; clear u.
  apply squash_rec'; intro b.
  change (chain_union_prelim chain x y a b = chain_union_prelim chain x y a' b).
  exact (chain_union_prelim_eq3 chain x y b a a').
Defined.

Definition chain_union_rel {X : hSet} {I : UU} {S : I → SubsetWithWellOrdering X}
           (chain : ∀ i j : I, S i ≼ S j ∨ S j ≼ S i) :
  hrel (carrier_set (⋃ (λ x : I, S x))).
Proof.
  intros x y.                 (* now define [x ≤ y] on the union *)
  simple refine (squash_to_set isasethProp _ _ (pr2 x)). (* x ∈ S i, for some i *)
  + exact (chain_union_prelim2     chain (pr1 x) y).
  + exact (chain_union_prelim2_eqn chain (pr1 x) y).
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
