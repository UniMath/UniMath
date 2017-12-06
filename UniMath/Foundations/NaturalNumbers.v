(** * Natural numbers and their properties. Vladimir Voevodsky. Apr. - Sep. 2011

This file contains the formulations and proofs of general properties of natural
numbers from the univalent perspecive. *)
(** ** Contents
- Equality and inequality on [nat]
 - Basic properties of [paths] on [nat] and the proofs of [isdeceq] and [isaset]
   for [nat]
 - [S : nat -> nat] is a decidable inclusion
- Inequalities on [nat]
 - Boolean "less of equal" and "greater or equal" on [nat]
 - Semi-boolean "greater" on [nat] or [natgth]
 - Semi-boolean "less" on [nat] or [natlth]
 - Semi-boolean "less or equal" on [nat] or [natleh]
 - Semi-boolean "greater or equal" on [nat] or [natgeh]
 - Simple implications between comparisons
 - Comparison alternatives
 - Mixed transitivities
 - Two comparisons and [S]
 - Comparison alternatives and [S]
- Some properties of [plus] on [nat]
 - The structure of the additive abelian monoid on [nat]
 - Addition and comparisons
 - Comparisons and [n -> n + 1]
 - Two comparisons and [n -> n + 1]
 - Comparison alternatives and [n -> n + 1]
 - Cancellation properties of [plus] on [nat]
 - Some properties of [minus] on [nat]
 - Basic algebraic properties of [mul] on [nat]
 - [nat] as a commutative rig
 - Cancellation properties of [mul] on [nat]
 - Multiplication and comparisons
 - Properties of comparisons in the terminology of algebra1.v
 - Submonoid of non-zero elements in [nat]
 - Division with a remainder on [nat]
 - Exponentiation [natpower n m] ("n to the power of m") on [nat]
 - Factorial on [nat]
- The order-preserving functions [di i : nat -> nat] whose image is the
  complement of one element [i].
- The order-preserving functions [si i : nat -> nat] that take the value [i]
  twice.
- Inductive types [le] with values in [UU]
 - A generalization of [le] and its properties
 - Inductive types [le] with values in [UU] are in [hProp]
 - Comparison between [le] with values in [UU] and [natleh]
*)


(** ** Preamble *)

(** Settings *)

(* The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.


(** Imports. *)
Require Export UniMath.Foundations.Sets.

(** To up-stream files  *)


(** ** Equality and inequality on [nat] *)

(* we will write m ≠ n for algorithmic inequality and ¬(m = n) for negation of
   equality *)

Definition natnegpaths (x y : nat) : hProp := hProppair (x != y) (isapropneg _).

Fixpoint natneq_hProp (n m : nat) : hProp :=
  match n, m with
  | S n, S m => natneq_hProp n m
  | O, O => hfalse
  | _, _ => htrue
  end.

(* Provisional notation, to be replaced below: *)
Notation " x ≠ y " := (natneq_hProp x y) (at level 70, no associativity) : nat_scope.

Local Open Scope nat_scope. (* it's already open, but we want it first in line *)

Lemma negpaths0sx (x : nat) : ¬ (0 = S x).
Proof.
  intro.
  set (f := λ n : nat, match n with O => true | S m => false end).
  apply (negf (@maponpaths _ _ f 0 (S x)) nopathstruetofalse).
Defined.

Lemma negpathssx0 (x : nat) : ¬ (S x = 0).
Proof.
  intros x X. apply (negpaths0sx x (pathsinv0  X)).
Defined.

Lemma invmaponpathsS (n m : nat) : S n = S m -> n = m.
Proof.
  intros n m e.
  set (f := λ n : nat, match n with O => O | S m => m end).
  apply (@maponpaths _ _ f (S n) (S m) e).
Defined.

Lemma noeqinjS (x x' : nat) : ¬ (x = x') -> ¬ (S x = S x').
Proof.
  intros x x'. apply (negf (invmaponpathsS x x')).
Defined.

Lemma natneq_iff_neq n m : ¬ (n = m) <-> n ≠ m.
Proof.
  intros n.
  induction n as [|n N].
  - intro m. induction m as [|m _].
    + apply logeq_both_false.
      * intro n. exact (n (idpath 0)).
      * simpl. exact (idfun ∅).
    + apply logeq_both_true.
      * apply negpaths0sx.
      * simpl. exact tt.
  - intro m. induction m as [|m _].
    + apply logeq_both_true.
      * apply negpathssx0.
      * simpl. exact tt.
    + split.
      * intro ne. apply (pr1 (N m)).
        intro r. exact (ne (maponpaths S r)).
      * intro neq. apply noeqinjS.
        apply (pr2 (N m)). exact neq.
Defined.

Lemma nat_neq_to_nopath {n m : nat} : ¬ (n = m) <- n ≠ m.
Proof.
  intros ? ?. exact (pr2 (natneq_iff_neq n m)).
Defined.

Lemma nat_nopath_to_neq {n m : nat} : ¬ (n = m) -> n ≠ m.
Proof.
  intros ? ?. exact (pr1 (natneq_iff_neq n m)).
Defined.

Definition natneq (m n : nat) : negProp (m = n).
Proof.
  intros. exists (m ≠ n). split.
  - apply propproperty.
  - apply natneq_iff_neq.
Defined.

(* this replaces the provisional notation above: *)
Notation " x ≠ y " := (natneq x y) (at level 70, no associativity) : nat_scope.

Local Open Scope nat_scope. (* it's already open, but we want it first in line *)

Lemma natneq0sx (x : nat) : 0 ≠ S x.
Proof.
  intro. apply nat_nopath_to_neq, negpaths0sx.
Defined.

Lemma natneqsx0 (x : nat) : S x ≠ 0.
Proof.
  intro. apply nat_nopath_to_neq, negpathssx0.
Defined.

Lemma natneqinjS (x x' : nat) : x ≠ x' -> S x ≠ S x'.
Proof.
  intros x x' r. apply nat_nopath_to_neq, noeqinjS, nat_neq_to_nopath. assumption.
Defined.

Lemma isirrefl_natneq i : ¬ (i ≠ i).
Proof.
  intros ? ne. apply (nat_neq_to_nopath ne). apply idpath.
Defined.

Lemma issymm_natneq i j : i ≠ j -> j ≠ i.
Proof.
  intros ? ? ne. apply nat_nopath_to_neq. intro eq. induction eq.
  exact (isirrefl_natneq j ne).
Defined.


(** *** Basic properties of [paths] on [nat] and the proofs of [isdeceq] and [isaset] for [nat]. *)

Definition isdeceqnat: isdeceq nat.
Proof.
  unfold isdeceq. intro x. induction x as [ | x IHx ].
  - intro x'. induction x'.
    + apply (ii1 (idpath O)).
    + apply (ii2 (negpaths0sx x')).
  - intro x'. induction x'.
    + apply (ii2 (negpathssx0 x)).
    + induction (IHx x') as [ p | e ].
      * apply (ii1 (maponpaths S  p)).
      * apply (ii2 (noeqinjS  _ _ e)).
Defined.

Definition isisolatedn (n : nat) : isisolated _ n.
Proof.
  intro. unfold isisolated. intro x'. apply isdeceqnat.
Defined.

Theorem isasetnat: isaset nat.
Proof.
  apply (isasetifdeceq _ isdeceqnat).
Defined.

Definition natset : hSet := hSetpair _ isasetnat.

Lemma nat_eq_or_neq (m n : nat) : (m = n) ⨿ (m ≠ n).
Proof.
  intros n. induction n as [|n N].
  - intro m. induction m as [|m _].
    + apply ii1. apply idpath.
    + apply ii2. exact tt.
  - intro m. induction m as [|m _].
    + apply ii2. exact tt.
    + induction (N m) as [eq|neq].
      * apply ii1, maponpaths. assumption.
      * apply ii2. assumption.
Defined.

Definition isdecrel_natneq : isdecrel natneq.
Proof.
  intros n. induction n as [|n N].
  - intro m. induction m as [|m _].
    + simpl. exact (ii2 (idfun ∅)).
    + simpl. exact (ii1 tt).
  - intro m. induction m as [|m _].
    + simpl. exact (ii1 tt).
    + exact (N m).
Defined.

Definition nateq (x y : nat) : hProp := hProppair (x = y) (isasetnat _ _).

Definition isdecrelnateq : isdecrel nateq := λ a b, isdeceqnat a b.

Definition natdeceq : decrel nat := decrelpair isdecrelnateq.

Definition natdecneq : decrel nat := decrelpair isdecrel_natneq.

Definition natboolneq : brel nat := decreltobrel natdecneq.


(** *** [ S : nat -> nat ] is a decidable inclusion. *)

Theorem isinclS : isincl S.
Proof.
  apply (isinclbetweensets S isasetnat isasetnat invmaponpathsS).
Defined.

Theorem isdecinclS : isdecincl S.
Proof.
  intro n. apply isdecpropif.
  - apply (isinclS n).
  - destruct n as [ | n ].
    + assert (nh : ¬ (hfiber S 0)).
      * intro hf. induction hf as [ m e ]. apply (negpathssx0 _ e).
      * apply (ii2 nh).
    + apply (ii1 (hfiberpair _ n (idpath _))).
Defined.


(** ** Inequalities on [nat]. *)


(** *** Boolean "less or equal" and "greater or equal" on [nat]. *)

Fixpoint natgtb (n m : nat) : bool :=
  match n, m with
  | S n, S m => natgtb n m
  | O, _ => false
  | _, _ => true
  end.


(** *** Semi-boolean "greater" on [nat] or [natgth]

1. Note that due to its definition [natgth] automatically has the property that
   [natgth n m <-> natgth (S n) (S m)] and the same applies to all other
   inequalities defined in this section.
2. We choose "greater" as the root relation from which we define all other
   relations on [nat] because it is more natural to extend "greater" to integers
   and then to rationals than it is to extend "less". *)


Definition natgth (n m : nat) : hProp := hProppair (natgtb n m = true) (isasetbool _ _).

Notation " x > y " := (natgth x y) : nat_scope.

Lemma negnatgth0n (n : nat) : ¬ (0 > n).
Proof.
  intro n. simpl. intro np. apply (nopathsfalsetotrue np).
Defined.

Lemma natgthsnn (n : nat) : S n > n.
Proof.
  intro. induction n as [ | n IHn ].
  - apply idpath.
  - apply IHn.
Defined.

Lemma natgthsn0 (n : nat) : S n > 0.
Proof.
  intro. simpl. apply idpath.
Defined.

Lemma negnatgth0tois0 (n : nat) (ng : ¬ (n > 0)) : n = 0.
Proof.
  intro. destruct n as [ | n ].
  - intro. apply idpath.
  - intro ng. induction (ng (natgthsn0 _)).
Defined.

Lemma natneq0togth0 (n : nat) (ne : n ≠ 0) : n > 0.
Proof.
  intros. destruct n as [ | n ].
  - induction ne.
  - apply natgthsn0.
Defined.

Lemma nat1gthtois0 (n : nat) (g : 1 > n) : n = 0.
Proof.
  intro. destruct n as [ | n ].
  - intro. apply idpath.
  - intro x. induction (negnatgth0n n x).
Defined.

Lemma istransnatgth (n m k : nat) : n > m -> m > k -> n > k.
Proof.
  intro. induction n as [ | n IHn ].
  - intros m k g. induction (negnatgth0n _ g).
  - intro m. destruct m as [ | m ].
    + intros k g g'. induction (negnatgth0n _ g').
    + intro k. destruct k as [ | k ].
      * intros. apply natgthsn0.
      * apply (IHn m k).
Defined.

Lemma isirreflnatgth (n : nat) : ¬ (n > n).
Proof.
  intro. induction n as [ | n IHn ].
  - apply (negnatgth0n 0).
  - apply IHn.
Defined.

Notation negnatlthnn := isirreflnatgth.

Lemma natgthtoneq (n m : nat) (g : n > m) : n ≠ m.
Proof.
  intros. apply nat_nopath_to_neq. intro e. rewrite e in g.
  apply (isirreflnatgth _ g).
Defined.

Lemma isasymmnatgth (n m : nat) : n > m -> m > n -> empty.
Proof.
  intros n m is is'.
  apply (isirreflnatgth n (istransnatgth _ _ _ is is')).
Defined.

Lemma isantisymmnegnatgth (n m : nat) : ¬ (n > m) -> ¬ (m > n) -> n = m.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros m ng0m ngm0. apply (pathsinv0 (negnatgth0tois0 _ ngm0)).
  - intro m. destruct m as [ | m ].
    + intros ngsn0 ng0sn. induction (ngsn0 (natgthsn0 _)).
    + intros ng1 ng2. apply (maponpaths S (IHn m ng1 ng2)).
Defined.

Lemma isdecrelnatgth : isdecrel natgth.
Proof.
  intros n m. apply (isdeceqbool (natgtb n m) true).
Defined.

Definition natgthdec := decrelpair isdecrelnatgth.

Lemma isnegrelnatgth : isnegrel natgth.
Proof.
  apply isdecreltoisnegrel. apply isdecrelnatgth.
Defined.

Lemma iscoantisymmnatgth (n m : nat) : ¬ (n > m) -> (m > n) ⨿ (n = m).
Proof.
  apply isantisymmnegtoiscoantisymm.
  - apply isdecrelnatgth.
  - intros n m. apply isantisymmnegnatgth.
Defined.

Lemma iscotransnatgth (n m k : nat) : n > k -> (n > m) ⨿ (m > k).
Proof.
  intros x y z gxz. induction (isdecrelnatgth x y) as [ p | np ].
  - apply ii1. assumption.
  - apply ii2. induction (isdecrelnatgth y x) as [r|nr].
    + apply (istransnatgth _ _ _ r gxz).
    + assert (e := isantisymmnegnatgth _ _ np nr); clear np nr.
      induction e. assumption.
Defined.


(** *** Semi-boolean "less" on [nat] or [natlth] *)

Definition natlth (n m : nat) := m > n.

Notation " x < y " := (natlth x y) : nat_scope.

Definition negnatlthn0 (n : nat) : ¬ (n < 0) := negnatgth0n n.

Definition natlthnsn (n : nat) : n < S n := natgthsnn n.

Definition negnat0lthtois0 (n : nat) (nl : ¬ (0 < n)) : n = 0 := negnatgth0tois0 n nl.

Definition natneq0to0lth (n : nat) : n ≠ 0 -> 0 < n := natneq0togth0 n.

Definition natlth1tois0 (n : nat) : n < 1 -> n = 0 := nat1gthtois0 _.

Definition istransnatlth (n m k : nat) : n < m -> m < k -> n < k :=
  λ lnm lmk, istransnatgth _ _ _ lmk lnm.

Definition isirreflnatlth (n : nat) : ¬ (natlth n n) := isirreflnatgth n.

Notation negnatgthnn := isirreflnatlth.

Lemma natlthtoneq (n m : nat) (g : natlth n m) : n ≠ m.
Proof.
  intros. apply nat_nopath_to_neq. intro e. rewrite e in g.
  apply (isirreflnatlth _ g).
Defined.

Definition isasymmnatlth (n m : nat) : natlth n m -> natlth m n -> empty :=
  λ lnm lmn, isasymmnatgth _ _ lmn lnm.

Definition isantisymmnegnattth  (n m : nat) :
  ¬ (natlth n m) -> ¬ (natlth m n) -> n = m := λ nlnm nlmn, isantisymmnegnatgth _ _ nlmn nlnm.

Definition isdecrelnatlth : isdecrel natlth := λ n m, isdecrelnatgth m n.

Definition natlthdec := decrelpair isdecrelnatlth.

Definition isnegrelnatlth : isnegrel natlth := λ n m, isnegrelnatgth m n.

Definition iscoantisymmnatlth (n m : nat) : ¬ (natlth n m) -> (natlth m n) ⨿ (n = m).
Proof.
  intros n m nlnm.
  induction (iscoantisymmnatgth m n nlnm) as [ l | e ].
  - apply (ii1 l).
  - apply (ii2 (pathsinv0 e)).
Defined.

Definition iscotransnatlth (n m k : nat) : n < k -> (n < m) ⨿ (m < k).
Proof.
  intros n m k lnk. apply coprodcomm, iscotransnatgth. assumption.
Defined.


(** *** Semi-boolean "less or equal " on [nat] or [natleh] *)

Definition natleh (n m : nat) := S m > n.

Notation " x <= y " := (natleh x y) : nat_scope.
Notation " x ≤ y " := (natleh x y) (at level 70, no associativity) : nat_scope.

Definition isdecrelnatleh : isdecrel natleh := λ m n, isdecrelnatgth _ _.

Definition negnatlehsn0 (n : nat) : ¬ (S n ≤ 0) := negnatlthn0 n.

(* these two lemmas show agreement with the old definition: *)

Lemma natlehneggth {n m : nat} : n ≤ m -> ¬ (n > m).
Proof.
  intro n. induction n as [|n N].
  - intros m _. exact (negnatgth0n m).
  - intros m. induction m as [|m _].
    + intros r _. exact (negnatlehsn0 n r).
    + exact (N m).
Defined.

Lemma natgthnegleh {n m : nat} : n > m -> ¬ (n ≤ m).
Proof.
  intros ? ? r s. exact (natlehneggth s r).
Defined.

Lemma negnatSleh n : ¬ (S n ≤ n).
Proof.
  intros. unfold natleh. apply isirreflnatgth.
Defined.

Lemma negnatgthtoleh {n m : nat} : ¬ (n > m) -> n ≤ m.
Proof.
  unfold natleh. intro n. induction n as [|n N].
  - intros m r. exact (natgthsn0 m).
  - intro m. change (S m > S n) with (m > n). induction m as [|m _].
    + intro r. contradicts (natgthsn0 n) r.
    + change (S n > S m) with (n > m). intro r. exact (N m r).
Defined.

Lemma negnatlehtogth {n m : nat} : n > m <- ¬ (n ≤ m).
Proof.
  intros ? ? r. apply (isdecreltoisnegrel isdecrelnatgth).
  intro s. exact (r (negnatgthtoleh s)).
Defined.

Definition neggth_logeq_leh (n m : nat) : ¬ (n > m) <-> n ≤ m := (negnatgthtoleh,,natlehneggth).

Definition natleh0tois0 {n : nat} (l : n ≤ 0) : n = 0 := natlth1tois0 n l.

Definition natleh0n (n : nat) : 0 ≤ n := natgthsn0 _.

Definition negnatlehsnn (n : nat) : ¬ (S n ≤ n) := isirreflnatlth _.

Definition istransnatleh {n m k : nat} : n ≤ m -> m ≤ k -> n ≤ k.
Proof.
  intros ? ? ? r s.
  apply negnatgthtoleh.
  assert (b := natlehneggth r); clear r.
  assert (c := natlehneggth s); clear s.
  intro r.
  induction (iscotransnatgth _ m _ r) as [t|t].
  - contradicts b t.
  - contradicts c t.
Defined.

Definition isreflnatleh n : n ≤ n.
Proof.
  intros. unfold natleh. apply natgthsnn.
Defined.

Definition isantisymmnatleh : isantisymm natleh.
Proof.
  intros m. induction m as [|m M].
  - intros n _ s. unfold natleh in s.
    apply pathsinv0. apply nat1gthtois0. exact s.
  - intros n. induction n as [|n _].
    + intros r _. contradicts r (negnatlehsn0 m).
    + intros r s.
      change (S m ≤ S n) with (m ≤ n) in r.
      change (S n ≤ S m) with (n ≤ m) in s.
      apply (maponpaths S).
      apply M.
      * assumption.
      * assumption.
Defined.

Definition natlehdec : decrel nat := decrelpair isdecrelnatleh.

Definition isnegrelnatleh : isnegrel natleh.
Proof.
  apply isdecreltoisnegrel. apply isdecrelnatleh.
Defined.

Definition natlthtoleh (m n : nat) : m < n -> m ≤ n.
Proof.
  intros ? ? r. unfold natleh. unfold natlth in r.
  generalize r. clear r. generalize m. clear m.
  induction n as [|n N].
  - intros ? r. contradicts r (negnatgth0n m).
  - intros ? r. induction m as [|m _].
    + apply natgthsn0.
    + change (S n > S m) with (n > m) in r.
      change (S (S n) > S m) with (S n > m).
      apply N. assumption.
Defined.

Definition iscoasymmnatleh (n m : nat) : ¬ (n ≤ m) -> m ≤ n.
Proof.
  intros ? ? r. apply negnatgthtoleh. intros s. unfold natleh in r.
  apply r. apply natlthtoleh. assumption.
Defined.

Definition istotalnatleh : istotal natleh.
Proof.
  intros x y. induction (isdecrelnatleh x y) as [ lxy | lyx ].
  - apply (hinhpr (ii1 lxy)).
  - apply hinhpr. apply ii2. apply (iscoasymmnatleh _ _ lyx).
Defined.


(** *** Semi-boolean "greater or equal" on [nat] or [natgeh]. *)

Definition natgeh (n m : nat) : hProp := m ≤ n.

Notation " x >= y " := (natgeh x y) : nat_scope.
Notation " x ≥ y " := (natgeh x y) (at level 70, no associativity) : nat_scope.

Definition nat0gehtois0 (n : nat) (g : 0 ≥ n) : n = 0 := natleh0tois0 g.

Definition natgehn0 (n : nat) : n ≥ 0 := natleh0n n.

Definition negnatgeh0sn (n : nat) : ¬ (0 ≥ (S n)) := negnatlehsn0 n.

Definition negnatgehnsn (n : nat) : ¬ (n ≥ (S n)) := negnatlehsnn n.

Definition istransnatgeh (n m k : nat) : n ≥ m -> m ≥ k -> n ≥ k := λ gnm gmk, istransnatleh gmk gnm.

Definition isreflnatgeh (n : nat) : n ≥ n := isreflnatleh _.

Definition isantisymmnatgeh (n m : nat) : n ≥ m -> m ≥ n -> n = m :=
  λ gnm gmn, isantisymmnatleh _ _ gmn gnm.

Definition isdecrelnatgeh : isdecrel natgeh := λ n m, isdecrelnatleh m n.

Definition natgehdec : decrel nat := decrelpair isdecrelnatgeh.

Definition isnegrelnatgeh : isnegrel natgeh := λ n m, isnegrelnatleh m n.

Definition iscoasymmnatgeh (n m : nat) (nl : ¬ (n ≥ m)) : m ≥ n := iscoasymmnatleh _ _ nl.

Definition istotalnatgeh : istotal natgeh := λ n m, istotalnatleh m n.

(** *** Simple implications between comparisons *)

Definition natgthtogeh (n m : nat) : n > m -> n ≥ m.
Proof.
  intros ? ?. apply natlthtoleh.
Defined.

Definition natlehtonegnatgth (n m : nat) : n ≤ m -> ¬ (n > m).
Proof.
  intros n m r. apply @natlehneggth. assumption.
Defined.

Definition  natgthtonegnatleh (n m : nat) : n > m -> ¬ (n ≤ m) := λ g l, natlehtonegnatgth _ _ l g.

Definition natgehtonegnatlth (n m : nat) :  n ≥ m -> ¬ (n < m) :=
  λ gnm lnm, natlehtonegnatgth _ _ gnm lnm.

Definition natlthtonegnatgeh (n m : nat) : n < m -> ¬ (n ≥ m) :=
  λ gnm lnm, natlehtonegnatgth _ _ lnm gnm.

Definition negnatgehtolth (n m : nat) : ¬ (n ≥ m) -> n < m.
Proof.
  intros ? ? r. apply negnatlehtogth. assumption.
Defined.

Definition negnatlthtogeh (n m : nat) : ¬ (n < m) -> n ≥ m := λ nl, negnatgthtoleh nl.

(* *** Simple corollaries of implications *** *)

Definition natlehnsn (n : nat) : n ≤ S n := natlthtoleh _ _ (natgthsnn n).

Definition natgehsnn (n : nat) : (S n) ≥ n := natlehnsn n.


(** *** Comparison alternatives *)

Definition natgthorleh (n m : nat) : (n > m) ⨿ (n ≤ m).
Proof.
  intros.
  induction (isdecrelnatgth n m) as [a|a].
  - apply ii1. assumption.
  - apply ii2. apply negnatgthtoleh. assumption.
Defined.

Definition natlthorgeh (n m : nat) : (n < m) ⨿ (n ≥ m) := natgthorleh _ _.

Definition natchoice0 (n : nat) : (0 = n) ⨿ (0 < n).
Proof.
  intros n. induction n as [ | n].
  - use ii1. apply idpath.
  - use ii2. apply natgthsn0.
Qed.

Definition natneqchoice (n m : nat) (ne : n ≠ m) : (n > m) ⨿ (n < m).
Proof.
  intros. induction (natgthorleh n m) as [ l | g ].
  - exact (ii1 l).
  - induction (natlthorgeh n m) as [ l' | g' ].
    + apply (ii2 l').
    + contradicts (nat_neq_to_nopath ne) (isantisymmnatleh _ _ g g').
Defined.

Definition natlehchoice (n m : nat) (l : n ≤ m) : (n < m) ⨿ (n = m).
Proof.
  intros. induction (natlthorgeh n m) as [ l' | g ].
  - apply (ii1 l').
  - apply (ii2 (isantisymmnatleh _ _ l g)).
Defined.

Definition natgehchoice (n m : nat) (g : n ≥ m) : (n > m) ⨿ (n = m).
Proof.
  intros. induction (natgthorleh n m) as [ g' | l ].
  - apply (ii1 g').
  - apply (ii2 (isantisymmnatleh _ _ l g)).
Defined.


(** *** Mixed transitivities *)

Lemma natgthgehtrans (n m k : nat) : n > m -> m ≥ k -> n > k.
Proof.
  intros n m k gnm gmk. induction (natgehchoice m k gmk) as [ g' | e ].
  - apply (istransnatgth _ _ _ gnm g').
  - rewrite e in gnm. apply gnm.
Defined.

Lemma natgehgthtrans (n m k : nat) : n ≥ m -> m > k -> n > k.
Proof.
  intros n m k gnm gmk. induction (natgehchoice n m gnm) as [ g' | e ].
  - apply (istransnatgth _ _ _ g' gmk).
  - rewrite e. apply gmk.
Defined.

Lemma natlthlehtrans (n m k : nat) : n < m -> m ≤ k -> n < k.
Proof.
  intros n m k l1 l2. apply (natgehgthtrans k m n l2 l1).
Defined.

Lemma natlehlthtrans (n m k : nat) : n ≤ m -> m < k -> n < k.
Proof.
  intros n m k l1 l2. apply (natgthgehtrans k m n l2 l1).
Defined.

Lemma natltltSlt (i j n : nat) : i < j -> j < S n -> i < n.
Proof.
  intros i j n l. apply natlthlehtrans. assumption.
Defined.


(** *** Two comparisons and [S] *)

Lemma natgthtogehsn (n m : nat) : n > m -> n ≥ (S m).
Proof.
  intro n. induction n as [ | n IHn ].
  - intros m X. induction (negnatgth0n _ X).
  - intros m X. destruct m as [ | m ].
    + apply (natgehn0 n).
    + apply (IHn m X).
Defined.

Lemma natgthsntogeh (n m : nat) : S n > m -> n ≥ m.
Proof.
  intros n m a. apply (natgthtogehsn (S n) m a).
Defined. (* PeWa *)

Lemma natgehtogthsn (n m : nat) : n ≥ m -> S n > m.
Proof.
  intros n m X. apply (natgthgehtrans _ n _).
  - apply natgthsnn.
  - apply X.
Defined.  (* New *)

Lemma natgehsntogth (n m : nat) : n ≥ (S m) -> n > m.
Proof.
  intros n m X.
  apply (natgehgthtrans _ (S m) _ X).
  apply natgthsnn.
Defined.  (* New *)

Lemma natlthtolehsn (n m : nat) : n < m -> S n ≤ m.
Proof.
  intros n m X. apply (natgthtogehsn m n X).
Defined.

Lemma natlehsntolth (n m : nat) : S n ≤ m -> n < m.
Proof.
  intros n m X. apply (natgehsntogth m n X).
Defined.

Lemma natlehtolthsn (n m : nat) : n ≤ m -> n < S m.
Proof.
  intros n m X. apply (natgehtogthsn m n X).
Defined.

Lemma natlthsntoleh (n m : nat) : n < S m -> n ≤ m.
Proof.
  intros n m a. apply (natlthtolehsn n (S m) a).
Defined. (* PeWa *)


(** *** Comparision alternatives and [S] *)

Lemma natlehchoice2 (n m : nat) : n ≤ m -> (S n ≤ m) ⨿ (n = m).
Proof.
  intros n m l. induction (natlehchoice n m l) as [ l' | e ].
  - apply (ii1 (natlthtolehsn _ _ l')).
  - apply (ii2 e).
Defined.

Lemma natgehchoice2 (n m : nat) : n ≥ m -> (n ≥ (S m)) ⨿ (n = m).
Proof.
  intros n m g. induction (natgehchoice n m g) as [ g' | e ].
  - apply (ii1 (natgthtogehsn _ _ g')).
  - apply (ii2 e).
Defined.

Lemma natgthchoice2 (n m : nat) : n > m -> (n > S m) ⨿ (n = (S m)).
Proof.
  intros n m g.
  induction (natgehchoice _ _ (natgthtogehsn _ _ g)) as [ g' | e ].
  - apply (ii1 g').
  - apply (ii2 e).
Defined.

Lemma natlthchoice2 (n m : nat) : n < m -> (S n < m) ⨿ ((S n) = m).
Proof.
  intros n m l.
  induction (natlehchoice _ _ (natlthtolehsn _ _ l)) as [ l' | e ].
  - apply (ii1 l').
  - apply (ii2 e).
Defined.


(** ** Some properties of [plus] on [nat] *)

(* Addition is defined in Init/Peano.v by the following code

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.
*)


(** *** The structure of the additive abelian monoid on [nat] *)

Lemma natplusl0 (n : nat) : (0 + n) = n.
Proof.
  intros. apply idpath.
Defined.

Lemma natplusr0 (n : nat) : (n + 0) = n.
Proof.
  intro. induction n as [ | n IH].
  - apply idpath.
  - simpl. apply (maponpaths S IH).
Defined.
Hint Resolve natplusr0: natarith.

Lemma natplusnsm (n m : nat) : n + S m = S n + m.
Proof.
  intro. simpl. induction n as [ | n IHn ].
  - auto with natarith.
  - simpl. intro. apply (maponpaths S (IHn m)).
Defined.
Hint Resolve natplusnsm : natarith.
Hint Resolve pathsinv0 : natarith.

Lemma natpluscomm (n m : nat) : n + m = m + n.
Proof.
  intro. induction n as [ | n IHn ].
  - intro.
    (*apply pathsinv0.*)
    (*apply natplusr0.*)
    auto with natarith.
  - intro. set (int := IHn (S m)).
    set (int2 := pathsinv0 (natplusnsm n m)).
    set (int3 := pathsinv0 (natplusnsm m n)).
    set (int4 := pathscomp0 int2 int).
    apply (pathscomp0 int4 int3).
Defined.
Hint Resolve natpluscomm : natarith.

Lemma natplusassoc (n m k : nat) : ((n + m) + k) = (n + (m + k)).
Proof.
  intro. induction n as [ | n IHn ].
  - auto with natarith.
  - intros. simpl. apply (maponpaths S (IHn m k)).
Defined.
Hint Resolve natplusassoc : natarith.


(** *** Addition and comparisons  *)

(** [natgth] *)

Definition natgthtogths (n m : nat) : n > m -> (S n) > m.
Proof.
  intros n m is. apply (istransnatgth _ _ _ (natgthsnn n) is).
Defined.

Definition negnatgthmplusnm (n m : nat) : ¬ (m > n + m).
Proof.
  intros. induction n as [ | n IHn ].
  - apply isirreflnatgth.
  - apply natlehtonegnatgth.
    assert (r := negnatgthtoleh IHn); clear IHn.
    apply (istransnatleh r (natlthtoleh _ _ (natlthnsn _))).
Defined.

Definition negnatgthnplusnm (n m : nat) : ¬ (n > (n + m)).
Proof.
  intros. rewrite (natpluscomm n m). apply (negnatgthmplusnm m n).
Defined.

Definition natgthandplusl (n m k : nat) : n > m -> (k + n) > (k + m).
Proof.
  intros n m k l. induction k as [ | k IHk ].
  - assumption.
  - assumption.
Defined.

Definition natgthandplusr (n m k : nat) : n > m -> (n + k) > (m + k).
Proof.
  intros.
  rewrite (natpluscomm n k). rewrite (natpluscomm m k).
  apply natgthandplusl.
  assumption.
Defined.

Definition natgthandpluslinv (n m k : nat) : (k + n) > (k + m) -> n > m.
Proof.
  intros n m k l. induction k as [ | k IHk ].
  - assumption.
  - apply (IHk l).
Defined.

Definition natgthandplusrinv (n m k : nat) : (n + k) > (m + k) -> n > m.
Proof.
  intros n m k l.
  rewrite (natpluscomm n k) in l.
  rewrite (natpluscomm m k) in l.
  apply (natgthandpluslinv _ _ _ l).
Defined.

Definition natgthandplusm (n m : nat) (H : m > 0) : n + m > n.
Proof.
  intros n. induction n as [ | n].
  - intros m H. rewrite natplusl0. exact H.
  - intros m H. rewrite <- natplusnsm. change (S n) with (1 + n). rewrite (natpluscomm 1 n).
    apply natgthandplusl. apply H.
Qed.

(** [natlth] *)

Definition natlthtolths (n m : nat) : n < m -> n < S m := natgthtogths _ _.

Definition negnatlthplusnmm (n m : nat) : ¬ (n + m < m) := negnatgthmplusnm _ _.

Definition negnatlthplusnmn (n m : nat) : ¬ (n + m < n) := negnatgthnplusnm _ _.

Definition natlthandplusl (n m k : nat) : n < m -> k + n < k + m := natgthandplusl _ _ _.

Definition natlthandplusr (n m k : nat) : n < m -> n + k < m + k := natgthandplusr _ _ _.

Definition natlthandpluslinv  (n m k : nat) : k + n < k + m -> n < m := natgthandpluslinv _ _ _.

Definition natlthandplusrinv (n m k : nat) : n + k < m + k -> n < m := natgthandplusrinv _ _ _.

Definition natlthandplusm (n m : nat) (H : 0 < m) : n < n + m := natgthandplusm _ _ H.

(** [natleh] *)

Definition natlehtolehs (n m : nat) : n ≤ m -> n ≤ S m.
Proof.
  intros n m is.
  apply (istransnatleh is (natlthtoleh _ _ (natlthnsn _))).
Defined.

Definition natlehmplusnm (n m : nat) : m ≤ n + m.
Proof.
  intros. induction n as [|n N].
  - change (0+m) with m. apply isreflnatleh.
  - apply natlehtolehs. assumption.
Defined.

Definition natlehnplusnm (n m : nat) : n ≤ n + m.
Proof.
  intros. induction m as [|m M].
  - induction (!natplusr0 n). apply isreflnatleh.
  - induction (plus_n_Sm n m). apply natlehtolehs. assumption.
Defined.

Definition natlehandplusl (n m k : nat) : n ≤ m ->  k + n ≤ k + m.
Proof.
  unfold natleh. intros ? ? ? r.
  rewrite (plus_n_Sm k m). apply natgthandplusl. assumption.
Defined.

Definition natlehandplusr (n m k : nat) : n ≤ m -> n + k ≤ m + k.
Proof.
  unfold natleh. intros ? ? ? r.
  change (S (m + k)) with (S m + k). apply natgthandplusr. assumption.
Defined.

Definition natlehandplus (i j k l : nat) : i ≤ j -> k ≤ l -> i + k ≤ j + l.
Proof.
  intros ? ? ? ? r s.
  use (@istransnatleh _ (j + k) _).
  - apply natlehandplusr. apply r.
  - apply natlehandplusl. apply s.
Defined.

Definition natlehandpluslinv (n m k : nat) : k + n ≤ k + m -> n ≤ m.
Proof.
  unfold natleh. intros ? ? ? r.
  rewrite (plus_n_Sm k m) in r.
  apply (natgthandpluslinv _ _ k). assumption.
Defined.

Definition natlehandplusrinv (n m k : nat) : n + k ≤ m + k -> n ≤ m.
Proof.
  unfold natleh. intros ? ? ? r.
  change (S (m + k)) with (S m + k) in r.
  apply (natgthandplusrinv _ _ k). assumption.
Defined.

(** [natgeh] *)

Definition natgehtogehs (n m : nat) : n ≥ m ->  S n ≥ m := natlehtolehs _ _.

Definition natgehplusnmm (n m : nat) : n + m ≥ m := natlehmplusnm _ _.

Definition natgehplusnmn (n m : nat) : n + m ≥ n := natlehnplusnm _ _.

Definition natgehandplusl (n m k : nat) : n ≥ m -> k + n ≥ k + m := natlehandplusl _ _ _.

Definition natgehandplusr (n m k : nat) : n ≥ m -> n + k ≥ m + k := natlehandplusr _ _ _.

Definition natgehandpluslinv  (n m k : nat) : k + n ≥ k + m -> n ≥ m := natlehandpluslinv _ _ _.

Definition natgehandplusrinv (n m k : nat) :  n + k ≥ m + k -> n ≥ m := natlehandplusrinv _ _ _.

(* The following are included mainly for direct compatibility with the library hz.v *)


(** *** Comparisons and [n -> n + 1] *)

Definition natgthtogthp1 (n m : nat) : n > m -> (n + 1) > m.
Proof.
  intros n m is. induction (natpluscomm 1 n).
  apply (natgthtogths n m is).
Defined.

Definition natlthtolthp1 (n m : nat) : n < m -> n < m + 1 := natgthtogthp1 _ _.

Definition natlehtolehp1 (n m : nat) : n ≤ m -> n ≤ m + 1.
Proof.
  intros n m is. induction (natpluscomm 1 m).
  apply (natlehtolehs n m is).
Defined.

Definition natgehtogehp1 (n m : nat) : n ≥ m -> (n + 1) ≥ m := natlehtolehp1 _ _.


(** *** Two comparisons and [n -> n + 1] *)

Lemma natgthtogehp1 (n m : nat) : n > m -> n ≥ (m + 1).
Proof.
  intros n m is. induction (natpluscomm 1 m).
  apply (natgthtogehsn n m is).
Defined.

Lemma natgthp1togeh (n m : nat) : (n + 1) > m -> n ≥ m.
Proof.
  intros n m is. induction (natpluscomm 1 n).
  apply (natgthsntogeh n m is).
Defined. (* PeWa *)

Lemma natlehp1tolth (n m : nat) : n + 1 ≤ m -> n < m.
Proof.
  intros n m is. induction (natpluscomm 1 n).
  apply (natlehsntolth n m is).
Defined.

Lemma natlthtolehp1 (n m : nat) : n < m -> n + 1 ≤  m.
Proof.
  intros n m is. induction (natpluscomm 1 n).
  apply (natlthtolehsn n m is).
Defined.

Lemma natlthp1toleh (n m : nat) : n < m + 1 -> n ≤ m.
Proof.
  intros n m is. induction (natpluscomm 1 m).
  apply (natlthsntoleh n m is).
Defined. (* PeWa *)

Lemma natgehp1togth (n m : nat) : n ≥ (m + 1) -> n > m.
Proof.
  intros n m is. induction (natpluscomm 1 m).
  apply (natgehsntogth n m is).
Defined.


(** *** Comparision alternatives and [n -> n + 1] *)

Lemma natlehchoice3 (n m : nat) : n ≤ m -> (n + 1 ≤ m) ⨿ (n = m).
Proof.
  intros n m l. induction (natlehchoice n m l) as [ l' | e ].
  - apply (ii1 (natlthtolehp1 _ _ l')).
  - apply (ii2 e).
Defined.

Lemma natgehchoice3 (n m : nat) : n ≥ m -> (n ≥ (m + 1)) ⨿ (n = m).
Proof.
  intros n m g. induction (natgehchoice n m g) as [ g' | e ].
  - apply (ii1 (natgthtogehp1 _ _ g')).
  - apply (ii2 e).
Defined.

Lemma natgthchoice3 (n m : nat) : n > m -> (n > (m + 1)) ⨿ (n = (m + 1)).
Proof.
  intros n m g.
  induction (natgehchoice _ _ (natgthtogehp1 _ _ g)) as [ g' | e ].
  - apply (ii1 g').
  - apply (ii2 e).
Defined.

Lemma natlthchoice3 (n m : nat) : n < m -> (n + 1 < m) ⨿ ((n + 1) = m).
Proof.
  intros n m l.
  induction (natlehchoice _ _ (natlthtolehp1 _ _ l)) as [ l' | e ].
  - apply (ii1 l').
  - apply (ii2 e).
Defined.

Lemma natlehchoice4 (n m : nat) : n < S m -> (n < m) ⨿ (n = m).
Proof.
  intros ? ? b.
  induction (natlthorgeh n m) as [p|p].
  - exact (ii1 p).
  - exact (ii2 (isantisymmnatleh _ _ (natlthsntoleh _ _ b) p)).
Defined.


(** *** Cancellation properties of [plus] on [nat] *)

Lemma pathsitertoplus (n m : nat) : (iteration S n m) = (n + m).
Proof.
  intros. induction n as [ | n IHn ].
  - apply idpath.
  - simpl. apply (maponpaths S IHn).
Defined.

Lemma isinclnatplusr (n : nat) : isincl (λ m : nat, m + n).
Proof.
  intro. induction n as [ | n IHn ].
  - apply (isofhlevelfhomot 1 _ _ (λ m : nat, pathsinv0 (natplusr0 m))).
    apply (isofhlevelfweq 1 (idweq nat)).
  - apply (isofhlevelfhomot 1 _ _ (λ m : nat, pathsinv0 (natplusnsm m n))).
    simpl. apply (isofhlevelfgf 1 _ _ isinclS IHn).
Defined.

Lemma isinclnatplusl (n : nat) : isincl (λ m : nat, n + m).
Proof.
  intro.
  apply (isofhlevelfhomot 1 _ _ (λ m : nat, natpluscomm m n) (isinclnatplusr n)).
Defined.

Lemma natplusrcan (a b c : nat) (is : a + c = b + c) : a = b.
Proof.
  intros. apply (invmaponpathsincl _ (isinclnatplusr c) a b). apply is.
Defined.

Lemma natpluslcan (a b c : nat) (is : c + a = c + b) : a = b.
Proof.
  intros. rewrite (natpluscomm _ _) in is.
  rewrite (natpluscomm c b) in is.
  apply (natplusrcan a b c  is).
Defined.

Lemma iscontrhfibernatplusr (n m : nat) (is : m ≥ n) : iscontr (hfiber (λ i : nat, i + n) m).
Proof.
  intros. apply iscontraprop1.
  - apply isinclnatplusr.
  - induction m as [ | m IHm ].
    + set (e := natleh0tois0 is). split with 0. apply e.
    + induction (natlehchoice2 _ _ is) as [ l | e ].
      * set (j := IHm l). induction j as [ j e' ]. split with (S j). simpl.
        apply (maponpaths S e').
      * split with 0. simpl. assumption.
Defined.

Lemma iscontrhfibernatplusl (n m : nat) (is : m ≥ n) : iscontr (hfiber (λ i : nat, n + i) m).
Proof.
  intros. apply iscontraprop1.
  - apply isinclnatplusl.
  - induction m as [ | m IHm ].
    + set (e := natleh0tois0 is). split with 0.
      rewrite <- plus_n_O. apply e.
    + induction (natlehchoice2 _ _ is) as [ l | e ].
      * set (j := IHm l). induction j as [ j e' ]. split with (S j). simpl.
        rewrite <- plus_n_Sm. apply (maponpaths S e').
      * split with 0. simpl. rewrite <- plus_n_O. assumption.
Defined.

Lemma neghfibernatplusr (n m : nat) (is : m < n) : ¬ (hfiber (λ i : nat, i + n) m).
Proof.
  intros. intro h. induction h as [ i e ]. rewrite (pathsinv0 e) in is.
  induction (natlehtonegnatgth _ _ (natlehmplusnm i n) is).
Defined.

Lemma isdecinclnatplusr (n : nat) : isdecincl (λ i : nat, i + n).
Proof.
  intros. intro m. apply isdecpropif.
  - apply (isinclnatplusr _ m).
  - induction (natlthorgeh m n) as [ ni | i ].
    + apply (ii2 (neghfibernatplusr n m ni)).
    + apply (ii1 (pr1 (iscontrhfibernatplusr n m i))).
Defined.


(** *** Some properties of [minus] on [nat]

Note : minus is defined in Init/Peano.v by the following code:

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.
*)

Definition minuseq0 (n m : nat) (is : n <= m) : n - m = 0.
Proof.
  intros n m. generalize n. clear n. induction m as [|m IHm].
  - intros n is. rewrite (natleh0tois0 is). simpl. apply idpath.
  - intro n. destruct n.
    + intro. apply idpath.
    + apply (IHm n).
Defined.

Definition minuseq0' (n : nat) : n - n = 0.
Proof.
  induction n as [|n I].
  - apply idpath.
  - simpl. exact I.
Defined.

Definition minusgth0 (n m : nat) (is : n > m) : n - m > 0.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros. induction (negnatgth0n _ is).
  - intro m. induction m as [ | m ].
    + intro. apply natgthsn0.
    + intro is. apply (IHn m is).
Defined.

Definition minusgth0inv (n m : nat) (is : n - m > 0) : n > m.
Proof.
  intro. induction n as [ | n IHn ].
  - intros. induction (negnatgth0n _ is).
  - intro. destruct m as [ | m ].
    + intros. apply natgthsn0.
    + intro. apply (IHn m is).
Defined.

Definition natminuseqn (n : nat) : n - 0 = n.
Proof.
  intro. destruct n. apply idpath. apply idpath.
Defined.

Definition natminuslehn (n m : nat) : n - m <= n.
Proof.
  intro n. induction n as [ | n IHn ].
  - intro. apply isreflnatleh.
  - intro. destruct m as [ | m ].
    + apply isreflnatleh.
    + simpl. apply (istransnatleh (IHn m) (natlehnsn n)).
Defined.

Definition natminusgehn (n m : nat) : n ≥ n - m := natminuslehn _ _.

Definition natminuslthn (n m : nat) (is : n > 0) (is' : m > 0) : n - m < n.
Proof.
  intro. induction n as [ | n IHn ].
  - intros. induction (negnatgth0n _ is).
  - intro m. induction m.
    + intros. induction (negnatgth0n _ is').
    + intros. apply (natlehlthtrans _ n _).
      * apply (natminuslehn n m).
      * apply natlthnsn.
Defined.

Definition natminuslthninv (n m : nat) (is : n - m < n) : m > 0.
Proof.
  intro. induction n as [ | n IHn ].
  - intros. induction (negnatlthn0 _ is).
  - intro m. destruct m as [ | m ].
    + intro. induction (negnatlthnn _ is).
    + intro. apply (natgthsn0 m).
Defined.

Definition minusplusnmm (n m : nat) (is : n ≥ m) : (n - m) + m = n.
Proof.
  intro n. induction n as [ | n IHn].
  - intro m. intro is. simpl. apply (natleh0tois0 is).
  - intro m. destruct m as [ | m ].
    + intro. simpl. rewrite (natplusr0 n). apply idpath.
    + simpl. intro is. rewrite (natplusnsm (n - m) m).
      apply (maponpaths S (IHn m is)).
Defined.

Definition minusplusnmmineq (n m : nat) : (n - m) + m ≥ n.
Proof.
  intros. induction (natlthorgeh n m) as [ lt | ge ].
  - rewrite (minuseq0 _ _ (natlthtoleh _ _ lt)).
    apply (natgthtogeh _ _ lt).
  - rewrite (minusplusnmm _ _ ge).
    apply isreflnatgeh.
Defined.

Definition plusminusnmm (n m : nat) : (n + m) - m = n.
Proof.
  intros.
  set (int1 := natgehplusnmm n m).
  apply (natplusrcan _ _ m).
  rewrite (minusplusnmm _ _ int1).
  apply idpath.
Defined.

Definition minusminusmmn (n m : nat) (H : m ≥ n) : m - (m - n) = n.
Proof.
  intros n m H.
  apply (natplusrcan (m - (m - n)) n (m - n)).
  - rewrite minusplusnmm.
    + rewrite natpluscomm. rewrite minusplusnmm.
      * apply idpath.
      * apply H.
    + apply natminusgehn.
Qed.

(** *** Comparisons and [n -> n - 1] *)

Definition natgthtogthm1 (n m : nat) : n > m -> n > m - 1.
Proof.
  intros n m is. induction m as [ | m].
  - apply is.
  - cbn. rewrite natminuseqn. apply (natgehgthtrans n (S m) m).
    + apply (natgthtogeh _ _ is).
    + apply natgthsnn.
Qed.

Definition natlthtolthm1 (n m : nat) : n < m -> n - 1 < m := natgthtogthm1 _ _.

Definition natlehtolehm1 (n m : nat) : n ≤ m -> n - 1 ≤ m := (fun X : n ≤ m => natlthtolthm1 n (S m) X).

Definition natgehtogehm1 (n m : nat) : n ≥ m -> n ≥ m - 1 := natlehtolehm1 _ _.

Definition natgthtogehm1 (n m : nat) : n > m -> n - 1 ≥ m.
Proof.
  intros n. induction n as [ | n].
  - intros m X. apply fromempty. apply (negnatgth0n m X).
  - intros m X. induction m as [ | m].
    + apply idpath.
    + cbn. rewrite natminuseqn. apply X.
Qed.

(* *** Two-sided minus and comparisons *)

Definition natgehandminusr (n m k : nat) (is : n ≥ m) : n - k ≥ m - k.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros. rewrite (nat0gehtois0 _ is). apply isreflnatleh.
  - intro m. induction m.
    + intros. destruct k.
      * apply natgehn0.
      * apply natgehn0.
    + intro k. induction k.
      * intro is. apply is.
      * intro is. apply (IHn m k is).
Defined.

Definition natgehandminusl (n m k : nat) (is : n ≥ m) : n - k ≥ m - k.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros. rewrite (nat0gehtois0 _ is). apply isreflnatleh.
  - intro m. induction m.
    + intros. destruct k.
      * apply natgehn0.
      * apply natgehn0.
    + intro k. induction k.
      * intro is. apply is.
      * intro is. apply (IHn m k is).
Defined.

Definition natgehandminusrinv (n m k : nat) (is' : n ≥ k) (is : n - k ≥ m - k) : n ≥ m.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros. rewrite (nat0gehtois0 _ is') in is.
    rewrite (natminuseqn m) in is. rewrite (nat0gehtois0 _ is).
    apply isreflnatleh.
  - intro m. induction m.
    + intros. apply natgehn0.
    + intros. destruct k.
      * rewrite natminuseqn in is. rewrite natminuseqn in is. apply is.
      * apply (IHn m k is' is).
Defined.

Definition natlthandminusl (n m i : nat) (is : n < m) (is' : i < m) : n - i < m - i.
Proof.
  intros n m i. induction i as [ | i].
  - intros is is'. rewrite natminuseqn. rewrite natminuseqn. apply is.
  - intros is is'.
    induction (natlthorgeh n (S i)) as [H | H].
    + assert (e : n - S i = 0).
      {
        apply minuseq0.
        exact (natlthtoleh _ _ H).
      }
      rewrite e. apply (natlthandplusrinv _ _ (S i)). rewrite natplusl0.
      rewrite minusplusnmm. apply is'.
      apply natlthtoleh. apply is'.
    + apply (natlthandplusrinv _ _ (S i)).
      rewrite (minusplusnmm m (S i)).
      * rewrite (minusplusnmm n (S i)).
        { apply is. }
        { apply H. }
      * apply natlthtoleh. apply is'.
Defined.

(*
Definition natgehandminuslinv (n m k : nat) (is' : natgeh k n)
(is : natleh  (k - n) (k - m)) : natgeh n m.
Proof.
intros.
set (int := natgehgthtrans _ (k - n) _ is (minusgeh0 _ _ is')).
set (int' := minusgeh0inv _ _ int).
set (int'' := natlehandplusr _ _ n is).
rewrite (minusplusnmm _ _ (natgthtogeh _ _ is')) in int''.
set (int''' := natlehandplusr _ _ m int'').
rewrite (natplusassoc _ n _) in int'''.
rewrite (natpluscomm n m) in int'''.
destruct (natplusassoc (k - m) m n) in int'''.
rewrite (minusplusnmm _ _ (natgthtogeh _ _ int')) in int'''.
apply (natgehandpluslinv _ _ k). apply int'''.
Defined.





induction n as [ | n IHn ]. intros.
rewrite (nat0gehtois0 _ is') in is.
rewrite (natminuseqn m) in is.
rewrite (nat0gehtois0 _ is).
apply isreflnatleh.
intro m. induction m. intros. apply natgehn0. intros.
destruct k.
rewrite natminuseqn in is. rewrite natminuseqn in is.
apply is. apply (IHn m k is is').
Defined.


(removed to lBsystems)
Definition natgthandminusinvr (n m k : nat) (is : natgth n m)
(is' : natgth n k) : natgth (n - k) (m - k).
Proof.
intro n. induction n as [ | n IHn ].
intros. destruct (negnatgth0n _ is). intro m. induction m. intros. destruct k.
apply natgthsn0. apply (IHapply natgehn0. intro k. induction k. intro is.
apply is. intro is.  apply (IHn m k is).
 Defined.



(removed to lBsystems)
Definition natlehandminusl (n m k : nat) (is : natgeh n m) :
natgeh (k - m) (k - n).
Proof.
intro n. induction n as [ | n IHn ].
intros. rewrite (nat0gehtois0 _ is).
apply isreflnatleh. intro m. induction m. intros.
destruct k.
apply natminuslehn. apply natminuslehn.
intro k. induction k. intro is.
apply isreflnatleh. intro is.
apply (IHn m k). apply is.
Defined.

Definition natlehandminusr

Definition natlthandminusl (n m k : nat) (is : natgth n m) (is' : natgeh k n) :
natlth (k - n) (k - m).
Proof.
intro n. induction n as [ | n IHn ].
intros. destruct (negnatgth0n _ is).
intro m. induction m. intros. destruct k.
destruct (negnatgeh0sn _ is').
apply (natlehlthtrans _ k _).
apply (natminuslehn k n).
apply natlthnsn.
intro k. induction k. intros is is'.
destruct (negnatgeh0sn _ is'). intros is is'.
apply (IHn m k is is').
Defined.

Definition natlehandminusl (n m k : nat) (is : natgeh n m) :
natleh (k - n) (k - m).
Proof.
intro n. induction n as [ | n IHn ].
intros. rewrite (nat0gehtois0 _ is).
apply isreflnatleh.
intro m. induction m. intros. destruct k.
apply natminuslehn. apply natminuslehn.
intro k. induction k. intro is.
apply isreflnatleh. intro is.
apply (IHn m k). apply is.
Defined.


Definition natlehandminusl (n m k : nat) : (n ≤ m) -> natgeh (k - n) (k - m)
:= natlehandminusl m n k.

Definition natlehandminusr (n m k : nat) : (n ≤ m) -> (n - k) ≤ (m - k)
:= natgehandminusr m n k.




(* *** One sided minus and comparisons *)


(* *** Greater or equal and minus *)

(* See lBsystems.v *)



(* **** Less and minus *)


Definition natlthrightminus (n m k : nat) (is : natlth (n + m) k) :
natlth n (k - m).

Definition natlthrightplus (n m k : nat) (is : natlth (n - m) k) :
natlth n (k + m).

Definition natlthleftminus (n m k : nat) (is : natlth n (m + k)) :
natlth (n - k) m.

Definition natlthleftplus (n m k : nat) (is : natlth n (m - k)) :
natlth (n + k) m.


(* **** Less or equal and minus *)


Definition natlehrightminus (n m k : nat) (is : (n + m) ≤ k) : n ≤ (k - m).

Definition natlehrightplus (n m k : nat) (is : (n - m) ≤ k) : n ≤ (k + m).

Definition natlehleftminus (n m k : nat) (is : n ≤ (m + k)) : (n - k) ≤ m.

Definition natlehleftplus (n m k : nat) (is : n ≤ (m - k)) : (n + k) ≤ m.










(* *** Mixed plus/minus associativities.

There are four possible plus/minus associativities which are labelled by
pp, pm, mp and mm depending on where in the side with the left parenthesis
one has minuses and where one has pluses. Two of those - pp and mm, are
unconditional. Two others require a condition to hold as equality and also
provide an unconditional inequality. Alltogether we have six statements
including a repeat of the usual pp associativity which we give here another
name in accrdance with the general naming scheme for these statements. *)

Notation natassocppeq := natplusassoc.

(* see lBsystems *)

Definition natassocpmineq (n m k : nat) : natleh ((n + m) - k) (n + (m - k)).
Proof.
intros n m k. destruct (natgthorleh k m) as [g | le].

set (e := minuseq0 m k (natgthtogeh _ _ g)).
rewrite e. rewrite (natplusr0 n).
destruct (boolchoice (natgtb k (n+m))) as [ g' | le'].
set (e' := minuseq0 (n+m) k (natgthtogeh _ _ g')).  rewrite e'.
apply natleh0n. apply (natlehandplusrinv _ _ k).
rewrite (minusplusnmm _ k).
apply natlehandplusl.
apply (natlthtoleh _ _ g).
set (int := falsetonegtrue _ le').
assumption.

rewrite (natassocpmeq _ _ _ le).
apply isreflnatleh.
Defined.


(* see lBsystems *)

Definition natassocmpineq (n m k : nat) : natgeh ((n - m) + k) (n - (m - k)).
Proof.
intros n m k. destruct (natgthorleh k m) as [g | le].

set (e := minuseq0 m k (natgthtogeh _ _ g)).
rewrite e. rewrite (natminuseqn n). apply (natgehandplusrinv _ _ m).
rewrite (natplusassoc _ _ m). rewrite (natpluscomm _ m).
destruct (natplusassoc (n - m) m k).
assert (int1 : natgeh (n - m + m + k) (n + k)).
apply (natgehandplusr _ _ k).
apply minusplusnmmineq.
assert (int2 : natgeh (n + k) (n + m)).
apply (natgehandplusl _ _ n).
apply (natgthtogeh _ _ g).
apply (istransnatgeh _ _ _ int1 int2).

destruct (natgthorleh m n) as [g' | le'].
rewrite (minuseq0 _ _ (natgthtogeh _ _ g')). change (0 + k) with k.
apply (natgehandplusrinv _ _ (m - k)).
rewrite (natpluscomm k _). rewrite (minusplusnmm _ _ le).

destruct (natgthorleh (m - k) n) as [ g'' | le'' ].
rewrite (minuseq0 n (m - k) (natgthtogeh _ _ g'')).
apply (natminuslehn  m k). rewrite (minusplusnmm _ _ le'').
apply (natgthtogeh _ _ g').

rewrite (natassocmpeq _ _ _ le' le). apply isreflnatgeh.
Defined.




Definition natassocpmineq (n m k : nat) : natleh ((n + m) - k) (n + (m - k)).
Proof.
intros n m k. destruct (natgthorleh k m) as [g | le].

set (e := minuseq0 m k (natgthtogeh _ _ g)).
rewrite e. rewrite (natplusr0 n).
destruct (boolchoice (natgtb k (n+m))) as [ g' | le'].
set (e' := minuseq0 (n+m) k (natgthtogeh _ _ g')). rewrite e'.
apply natleh0n. apply (natlehandplusrinv _ _ k).
rewrite (minusplusnmm _ k). apply natlehandplusl.
apply (natlthtoleh _ _ g). set (int := falsetonegtrue _ le').
assumption.

rewrite (natassocpmeq _ _ _ le). apply isreflnatleh. Defined.
*)


(** *** Basic algebraic properties of [mul] on [nat].

  We no longer user [mult]. *)

Lemma natmult0n (n : nat) : (0 * n) = 0.
Proof.
  intro n. apply idpath.
Defined.
Hint Resolve natmult0n : natarith.

Lemma natmultn0 (n : nat) : n * 0 = 0.
Proof.
  intro n.
  induction n as [ | n IHn ].
  - apply idpath.
  - simpl. exact (natplusr0 _ @ IHn).
Defined.
Hint Resolve natmultn0 : natarith.

Lemma multsnm (n m : nat) : S n * m = m + n * m.
Proof.
  intros. simpl. apply natpluscomm.
Defined.
Hint Resolve multsnm : natarith.

Lemma multnsm (n m : nat) : n * S m = n + n * m.
Proof.
  intro n.
  induction n as [|n IHn].
  - intros.
    apply idpath.
  - intro m. simpl.
    rewrite <- natplusassoc.
    rewrite (natpluscomm _ m).
    change (S (m + (n + n * m))) with (S m + (n + n * m)).
    rewrite (natpluscomm (S m) _).
    apply (maponpaths (λ x, x + S m)).
    apply IHn.
Defined.
Hint Resolve multnsm : natarith.

Lemma natmultcomm (n m : nat) : (n * m) = (m * n).
Proof.
  intro. induction n as [ | n IHn ].
  - intro. auto with natarith.
  - intro m. rewrite (multsnm n m). rewrite (multnsm m n).
    apply (maponpaths (λ x : _, m + x) (IHn m)).
Defined.

Lemma natrdistr (n m k : nat) : (n + m) * k = n * k + m * k.
Proof.
  intros.
  induction n as [ | n IHn ].
  - apply idpath.
  - simpl.
    rewrite natplusassoc. rewrite (natpluscomm k _).
    rewrite <- natplusassoc.
    exact (maponpaths (λ x, x+k) IHn).
Defined.

Lemma natldistr (m k n : nat) : (n * (m + k)) = (n * m + n * k).
Proof.
  intros m k n. induction m as [ | m IHm ].
  - simpl. rewrite (natmultn0 n). auto with natarith.
  - simpl. rewrite (multnsm n (m + k)). rewrite (multnsm n m).
    rewrite (natplusassoc _ _ _).
    apply (maponpaths (λ x : _, n + x) (IHm)).
Defined.

Lemma natmultassoc (n m k : nat) : ((n * m) * k) = (n * (m * k)).
Proof.
  intros.
  induction n as [ | n IHn ].
  - apply idpath.
  - simpl.
    rewrite natrdistr.
    apply (maponpaths (λ x, x + m * k)).
    apply IHn.
Defined.

Lemma natmultl1 (n : nat) : (1 * n) = n.
Proof.
  simpl. auto with natarith.
Defined.
Hint Resolve natmultl1 : natarith.

Lemma natmultr1 (n : nat) : (n * 1) = n.
Proof.
  intro n. rewrite (natmultcomm n 1). auto with natarith.
Defined.
Hint Resolve natmultr1 : natarith.

(** *** Cancellation properties of [mul] on [nat] *)

Definition natplusnonzero (n m : nat) : m ≠ 0 -> n+m ≠ 0.
Proof.
  intros ? ? ne. induction n as [|n]; easy.
Defined.

Definition natneq0andmult (n m : nat) : n ≠ 0 -> m ≠ 0 -> n * m ≠ 0.
Proof.
  intros ? ? isn ism. induction n as [|n].
  - easy.
  - clear isn. simpl. apply natplusnonzero. assumption.
Defined.

Definition natneq0andmultlinv (n m : nat) : n * m ≠ 0 -> n ≠ 0.
Proof.
  induction n as [|n _].
  - intros ? r. easy.
  - intros _ _. apply natneqsx0.
Defined.

Definition natneq0andmultrinv (n m : nat) : n * m ≠ 0 -> m ≠ 0.
Proof.
  induction m as [|m _].
  - intro r. apply fromempty. apply (nat_neq_to_nopath r), natmultn0.
  - intros _. apply natneqsx0.
Defined.

(** *** Multiplication and comparisons  *)

(** [natgth] *)

Definition natgthandmultl (n m k : nat) : k ≠ 0 -> n > m -> (k * n) > (k * m).
Proof.
  intro n. induction n as [ | n IHn ].
  - intros m k g g'. induction (negnatgth0n _ g').
  - intro m. destruct m as [ | m ].
    + intros k g g'.
      rewrite (natmultn0 k). rewrite (multnsm k n).
      apply (natgehgthtrans _ _ _ (natgehplusnmn k (k* n)) (natneq0togth0 _ g)).
    + intros k g g'. rewrite (multnsm k n). rewrite (multnsm k m).
      apply (natgthandplusl _ _ _). apply (IHn m k g g').
Defined.

Definition natgthandmultr (n m k : nat) : k ≠ 0 -> n > m -> (n * k) > (m * k).
Proof.
  intros n m k l. rewrite (natmultcomm n k). rewrite (natmultcomm m k).
  apply (natgthandmultl n m k l).
Defined.

Definition natgthandmultlinv (n m k : nat) : (k * n) > (k * m) -> n > m.
Proof.
  intro n. induction n as [ | n IHn ].
  - intros m k g. rewrite (natmultn0 k) in g. induction (negnatgth0n _ g).
  - intro m. destruct m as [ | m ].
    + intros. apply (natgthsn0 _).
    + intros k g. rewrite (multnsm k n) in g. rewrite (multnsm k m) in g.
      apply (IHn m k (natgthandpluslinv _ _ k g)).
Defined.

Definition natgthandmultrinv (n m k : nat) : (n * k) > (m * k) -> n > m.
Proof.
  intros n m k g.
  rewrite (natmultcomm n k) in g. rewrite (natmultcomm m k) in g.
  apply (natgthandmultlinv n m k g).
Defined.

(** [natlth] *)

Definition natlthandmultl (n m k : nat) : k ≠ 0 -> n < m -> k * n < k * m := natgthandmultl _ _ _.

Definition natlthandmultr (n m k : nat) : k ≠ 0 -> n < m -> n * k < m * k := natgthandmultr _ _ _.

Definition natlthandmultlinv (n m k : nat) : k * n < k * m -> n < m := natgthandmultlinv _ _ _.

Definition natlthandmultrinv (n m k : nat) : n * k < m * k -> n < m := natgthandmultrinv _ _ _.

(** [natleh] *)

Definition natlehandmultl (n m k : nat) : n ≤ m -> k * n ≤ k * m.
Proof.
  intros ? ? ? r. apply negnatgthtoleh; intro t.
  apply (natlehtonegnatgth _ _ r). apply (natgthandmultlinv _ _ k). assumption.
Defined.

Definition natlehandmultr (n m k : nat) : n ≤ m -> n * k ≤ m * k.
Proof.
  intros ? ? ? r. apply negnatgthtoleh; intro t.
  apply (natlehtonegnatgth _ _ r).
  apply (natgthandmultrinv _ _ k). assumption.
Defined.

Definition natlehandmultlinv (n m k : nat) : k ≠ 0 -> k * n ≤ k * m -> n ≤ m.
Proof.
  intros ? ? ? r s. apply negnatgthtoleh; intro t.
  apply (natlehtonegnatgth _ _ s).
  apply (natgthandmultl _ _ _ r). assumption.
Defined.

Definition natlehandmultrinv (n m k : nat) : k ≠ 0 -> n * k ≤ m * k -> n ≤ m.
Proof.
  intros ? ? ? r s. apply negnatgthtoleh; intro t.
  apply (natlehtonegnatgth _ _ s).
  apply (natgthandmultr _ _ _ r). assumption.
Defined.

(** [natgeh] *)

Definition natgehandmultl (n m k : nat) : n ≥ m -> (k * n) ≥ (k * m) := natlehandmultl _ _ _.

Definition natgehandmultr (n m k : nat) : n ≥ m -> (n * k) ≥ (m * k) := natlehandmultr _ _ _.

Definition natgehandmultlinv (n m k : nat) : k ≠ 0 -> k * n ≥ k * m -> n ≥ m := natlehandmultlinv _ _ _.

Definition natgehandmultrinv (n m k : nat) : k ≠ 0 -> n * k ≥ m * k -> n ≥ m := natlehandmultrinv _ _ _.

(** *** Division with a remainder on [nat]

For technical reasons it is more convenient to introduce divison with remainder
for all pairs (n,m) including pairs of the form (n,0). *)

Definition natdivrem (n m : nat) : dirprod nat nat.
Proof.
  intros. induction n as [ | n IHn ].
  - intros. apply (dirprodpair 0 0).
  - induction (natlthorgeh (S (pr2 IHn)) m).
    + apply (dirprodpair (pr1 IHn) (S (pr2 IHn))).
    + apply (dirprodpair (S (pr1 IHn)) 0).
Defined.

Definition natdiv (n m : nat) : nat := pr1 (natdivrem n m).

Definition natrem (n m : nat) : nat := pr2 (natdivrem n m).

Notation " x /+ y " := (natrem x y) (at level 40, left associativity) : nat_scope.
Notation " x / y " := (natdiv x y) (at level 40, left associativity) : nat_scope.

Lemma lthnatrem (n m : nat) : m ≠ 0 -> n /+ m < m.
Proof.
  unfold natrem. intros ? ? is. destruct n as [ | n ].
  - simpl. intros. apply (natneq0togth0 _ is).
  - simpl. induction (natlthorgeh (S (pr2 (natdivrem n m))) m) as [ nt | t ].
    + simpl. apply nt.
    + simpl. apply (natneq0togth0 _ is).
Defined.

Theorem natdivremrule (n m : nat) (is : m ≠ 0) : n = ((natrem n m) + (natdiv n m) * m).
Proof.
  intro. induction n as [ | n IHn ].
  - simpl. intros. apply idpath.
  - intros m is. unfold natrem. unfold natdiv. simpl.
    induction (natlthorgeh (S (pr2 (natdivrem n m))) m)  as [ nt | t ].
    + simpl. apply (maponpaths S (IHn m is)).
    + simpl. set (is' := lthnatrem n m is).
      induction (natgthchoice2 _ _ is') as [ h | e ].
      induction (natlehtonegnatgth _ _ t h).
      fold (natdiv n m).
      set (e'' := maponpaths S (IHn m is)).
      change (S (natrem n m + natdiv n m * m))
      with (S (natrem n m) + natdiv n m * m) in e''.
      rewrite (pathsinv0 e) in e''. rewrite (natpluscomm _ m).
      apply e''.
Defined.
Opaque natdivremrule.

Lemma natlehmultnatdiv (n m : nat) (is : m ≠ 0) : natdiv n m * m ≤ n.
Proof.
  intros.
  set (e := natdivremrule n m is).
  set (int := (natdiv n m) * m).
  rewrite e.              (* why can't we just say "rewrite e at 2" here? *)
  apply natlehmplusnm.
Defined.

Theorem natdivremunique (m i j i' j' : nat) (lj : j < m) (lj' : j' < m)
        (e : j + i * m = j' + i' * m) :  i = i' × j = j'.
Proof.
  intros m i. induction i as [ | i IHi ].
  - intros ? ? ? lj lj'.
    simpl.
    intro e.
    simpl in e.
    rewrite natplusr0 in e.
    rewrite e in lj.
    induction i'.
    + simpl in e.
      rewrite natplusr0 in e.
      exact (idpath _,,e).
    + change (S i' * m) with (i' * m + m) in lj.
      rewrite <- natplusassoc in lj.
      induction (negnatgthmplusnm _ _ lj).
  - intros ? ? ? lj lj' e.
    induction i' as [ | i' ].
    + simpl in e.
      rewrite natplusr0 in e.
      rewrite <- e in lj'.
      rewrite <- natplusassoc in lj'.
      induction (negnatgthmplusnm _ _ lj').
    + simpl in e.
      rewrite <- (natplusassoc j) in e.
      rewrite <- (natplusassoc j') in e.
      set (e' := invmaponpathsincl _ (isinclnatplusr m) _ _ e).
      set (ee := IHi j i' j' lj lj' e').
      exact (dirprodpair (maponpaths S (pr1 ee)) (pr2 ee)).
Defined.
Opaque natdivremunique.

Lemma natdivremandmultl (n m k : nat) (ism : m ≠ 0) (iskm : (k * m) ≠ 0) :
  dirprod (paths (natdiv (k * n) (k * m)) (natdiv n m))
          (paths (natrem (k * n) (k * m)) (k * (natrem n m))).
Proof.
  intros.
  set (ak := natdiv (k * n) (k * m)).
  set (bk := natrem (k * n) (k * m)).
  set (a := natdiv n m). set (b := natrem n m).
  assert (e1 : paths (bk + ak * (k * m)) ((b * k) + a * (k * m))).
  {
    unfold ak. unfold bk.
    rewrite (pathsinv0 (natdivremrule (k * n) (k * m) iskm)).
    rewrite (natmultcomm k m).
    rewrite (pathsinv0 (natmultassoc _ _ _)).
    rewrite (pathsinv0 (natrdistr _ _ _)).
    unfold a. unfold b.
    rewrite (pathsinv0 (natdivremrule n m ism)).
    apply (natmultcomm k n).
  }
  set (l1 := lthnatrem n m ism).
  set (l1' := (natlthandmultr _ _ _ (natneq0andmultlinv _ _ iskm) l1)).
  rewrite (natmultcomm m k) in l1'.
  set (int := natdivremunique
                _ _ _ _ _ (lthnatrem (k * n) (k * m) iskm) l1' e1).
  split with (pr1 int).
  rewrite (natmultcomm k b). apply (pr2 int).
Defined.
Opaque natdivremandmultl.

Definition natdivandmultl (n m k : nat) (ism : m ≠ 0) (iskm : (k * m) ≠ 0) :
  paths (natdiv (k * n) (k * m)) (natdiv n m) := pr1 (natdivremandmultl _ _ _ ism iskm).

Definition natremandmultl (n m k : nat) (ism : m ≠ 0) (iskm : (k * m) ≠ 0) :
  paths (natrem (k * n) (k * m)) (k * (natrem n m)) := pr2 (natdivremandmultl _ _ _ ism iskm).

Lemma natdivremandmultr (n m k : nat) (ism : m ≠ 0) (ismk : (m * k) ≠ 0) :
  dirprod (paths (natdiv (n * k) (m * k)) (natdiv n m))
          (paths (natrem (n * k) (m * k)) ((natrem n m) * k)).
Proof.
  intros. rewrite (natmultcomm m k). rewrite (natmultcomm m k) in ismk.
  rewrite (natmultcomm n k). rewrite (natmultcomm (natrem _ _) k).
  apply (natdivremandmultl _ _ _ ism ismk).
Defined.
Opaque natdivremandmultr.

Definition natdivandmultr (n m k : nat) (ism : m ≠ 0) (ismk : (m * k) ≠ 0) :
  paths (natdiv (n * k) (m * k)) (natdiv n m) := pr1 (natdivremandmultr _ _ _ ism ismk).

Definition natremandmultr (n m k : nat) (ism : m ≠ 0) (ismk : (m * k) ≠ 0) :
  natrem (n * k) (m * k) = (natrem n m) * k := pr2 (natdivremandmultr _ _ _ ism ismk).


(** *** Exponentiation [natpower n m] ("n to the power m") on [nat] *)

Fixpoint natpower (n m : nat) : nat :=
  match m with
  | O => 1
  | S m' => n * (natpower n m')
  end.


(** *** Factorial on [nat] *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (S n') * (factorial n')
  end.


(** ** The order-preserving functions [di i : nat -> nat] whose image is the complement of one element [i]. *)

Definition di (i : nat) (x : nat) : nat :=
  match natlthorgeh x i with
  | ii1 _ => x
  | ii2 _ => S x
  end.

Lemma di_eq1 {i x} : x < i → di i x = x.
Proof.
  intros ? ? lt. unfold di.
  induction (natlthorgeh x i) as [_|P].
  - apply idpath.
  - apply fromempty. exact (natgehtonegnatlth _ _ P lt).
Defined.

Lemma di_eq2 {i x} : x ≥ i → di i x = S x.
Proof.
  intros ? ? lt. unfold di.
  induction (natlthorgeh x i) as [P|_].
  - apply fromempty. exact (natlthtonegnatgeh _ _ P lt).
  - apply idpath.
Defined.

Lemma di_neq_i (i x : nat) : i ≠ di i x.
Proof.
  intros. apply nat_nopath_to_neq. intro eq.
  unfold di in eq. induction (natlthorgeh x i) as [lt|ge].
  - induction eq. exact (isirreflnatlth i lt).
  - induction (!eq); clear eq. exact (negnatgehnsn _ ge).
Defined.

Lemma natlehdinsn (i n : nat) : (di i n) ≤ (S n).
Proof.
  intros. unfold di. induction (natlthorgeh n i).
  - apply natlthtoleh. apply natlthnsn.
  - apply isreflnatleh.
Defined.

Lemma natgehdinn (i n : nat) : (di i n) ≥ n.
Proof.
  intros. unfold di. induction (natlthorgeh n i).
  - apply isreflnatleh.
  - apply natlthtoleh. apply natlthnsn.
Defined.

Lemma isincldi (i : nat) : isincl (di i).
Proof.
  intro. apply (isinclbetweensets (di i) isasetnat isasetnat).
  intros x x'. unfold di. intro e.
  induction (natlthorgeh x i) as [ l | nel ].
  - induction (natlthorgeh x' i) as [ l' | nel' ].
    + apply e.
    + rewrite e in l. assert (e' := natgthtogths _ _  l).
      change (S i > S x') with (i > x') in e'.
      contradicts (natlehtonegnatgth _ _ nel') e'.
  - induction  (natlthorgeh x' i)  as [ l' | nel' ].
    + induction e.
      set (e' := natgthtogths _ _ l').
      contradicts (natlehtonegnatgth _ _ nel) e'.
    + apply (invmaponpathsS _ _ e).
Defined.

Lemma neghfiberdi (i : nat) : ¬ (hfiber (di i) i).
Proof.
  intros i hf. unfold di in hf. induction hf as [ j e ].
  induction (natlthorgeh j i) as [ l | g ]. induction e.
  apply (isirreflnatlth _ l). induction e in g. apply (negnatgehnsn _ g).
Defined.

Lemma iscontrhfiberdi (i j : nat) (ne : i ≠ j) : iscontr (hfiber (di i) j).
Proof.
  intros. apply iscontraprop1. apply (isincldi i j).
  induction (natlthorgeh j i) as [ l | nel ].
  - split with j. unfold di.
    induction (natlthorgeh j i) as [ l' | nel' ].
    + apply idpath.
    + contradicts (natlehtonegnatgth _ _ nel') l.
  - induction (natgehchoice2 _ _ nel) as [ g | e ].
    destruct j as [ | j ].
    + induction (negnatgeh0sn _ g).
    + split with j. unfold di. induction (natlthorgeh j i) as [ l' | g' ].
      * contradicts (natlehtonegnatgth _ _ g) l'.
      * apply idpath.
    + induction ((nat_neq_to_nopath ne) (pathsinv0 e)).
Defined.

Lemma isdecincldi (i : nat) : isdecincl (di i).
Proof.
  intros i j. apply isdecpropif.
  - apply (isincldi i j).
  - induction (nat_eq_or_neq i j)  as [ eq | neq ].
    + apply ii2. induction eq.  apply (neghfiberdi i).
    + apply ii1. apply (pr1 (iscontrhfiberdi i j neq)).
Defined.


(** ** The order-preserving functions [si i : nat -> nat] that take the value [i] twice. *)

Definition si (i : nat) (x : nat) : nat :=
  match natlthorgeh i x with
    | ii1 _ => x - 1
    | ii2 _ => x
  end.

Definition nat_compl (i : nat) := compl_ne _ i (λ j, i ≠ j).

Lemma natleh_neq {i j : nat} : i ≤ j -> i ≠ j -> i < j.
Proof.
  intros ? ? le ne.
  induction (natlehchoice _ _ le) as [lt|eq].
  - exact lt.
  - induction eq. apply fromempty. exact (isirrefl_natneq _ ne).
Defined.

Theorem weqdicompl (i : nat) : nat ≃ nat_compl i.
Proof.
  intros i.
  use weqgradth.
  - intro j. exists (di i j). apply di_neq_i.
  - intro j. exact (si i (pr1 j)).
  - simpl. intro j. unfold di. induction (natlthorgeh j i) as [lt|ge].
    + unfold si. induction (natlthorgeh i j) as [lt'|ge'].
      * contradicts (isasymmnatlth _ _ lt') lt.
      * apply idpath.
    + unfold si. induction (natlthorgeh i (S j)) as [lt'|ge'].
      * change (S j) with (1 + j). rewrite natpluscomm. apply plusminusnmm.
      * unfold natgeh,natleh in ge. contradicts (natlehneggth ge') ge.
  - simpl. intro j. induction j as [j ne]; simpl.
    apply subtypeEquality.
    + intro k. apply negProp_to_isaprop.
    + simpl. unfold si. induction (natlthorgeh j i) as [lt|ge].
      * clear ne.
        induction (natlthorgeh i j) as [lt'|_].
        { contradicts (isasymmnatlth _ _ lt') lt. }
        { unfold di. induction (natlthorgeh j i) as [lt'|ge'].
          - apply idpath.
          - contradicts (natgehtonegnatlth _ _ ge') lt. }
      * assert (lt := natleh_neq ge ne); clear ne ge.
        induction (natlthorgeh i j) as [_|ge'].
        { unfold di. induction (natlthorgeh (j - 1) i) as [lt'|ge'].
          - apply fromempty. induction j as [|j _].
            + exact (negnatlthn0 _ lt).
            + change (S j) with (1 + j) in lt'.
                 rewrite natpluscomm in lt'.
                 rewrite plusminusnmm in lt'.
                 change (i < S j) with (i ≤ j) in lt.
                 exact (natlehneggth lt lt').
          - induction j as [|j _].
            + contradicts (negnatlthn0 i) lt.
            + simpl. apply maponpaths. apply natminuseqn. }
        contradicts (natgehtonegnatlth _ _ ge') lt.
Defined.


(* more lemmas about natural numbers *)

Lemma natminusminus (n i j : nat) : n - i - j = n - (i + j).
Proof.
  intros n; induction n as [|n N].
  - intros. apply idpath.
  - intros i; induction i as [|i _].
    + intros. apply idpath.
    + apply N.
Defined.

Lemma natltplusS (n i : nat) : i < i + S n.
Proof.
  intros. rewrite <- (natplusr0 i).
  rewrite natplusassoc. apply natlthandplusl. apply idpath.
Defined.

Lemma nat_split {n m i : nat} : (i < n + m) -> (i ≥ n) -> i - n < m.
Proof.
  intros n m i p H.
  induction (plusminusnmm m n).
  apply natlthandminusl.
  - induction (natpluscomm n m). exact p.
  - induction (natpluscomm n m). apply (natlehlthtrans _ i).
    * assumption.
    * assumption.
Defined.

Lemma natplusminusle {a b c} : b ≥ c -> a+(b-c) = (a+b)-c.
Proof.
  intros ? ? ? e. assert (E := minusplusnmm b c e). rewrite <- E. clear E e.
  rewrite <- natplusassoc. rewrite plusminusnmm. rewrite plusminusnmm. apply idpath.
Defined.

Lemma natdiffplusdiff {a b c} : a ≥ b -> b ≥ c -> a-c = (a-b) + (b-c).
Proof.
  intros ? ? ? r s. apply (natplusrcan _ _ c). rewrite natplusassoc.
  rewrite (minusplusnmm _ _ s). rewrite (minusplusnmm _ _ (istransnatleh s r)).
  exact (! minusplusnmm _ _ r).
Defined.
