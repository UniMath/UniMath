(**
Auke Booij
Nov. 2017


If [ P ] is a decidable predicate on the natural numbers, then from the existence of a natural
number satisfying [ P ], we can find a natural number satisfying [ P ].
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Propositions.

Section constr_indef_descr.
  Context
    (P : nat → hProp)
    (P_dec : ∏ n : nat, P n ⨿ ¬ P n)
    (P_inhab : ∃ n : nat, P n).

  Local Definition minimal (n : nat) : UU := ∏ m : nat, P m → (n ≤ m).
  Local Definition isapropminimal (n : nat) : isaprop (minimal n).
  Proof.
    apply impred_isaprop.
    intros m.
    apply isapropimpl.
    apply isasetbool.
  Defined.

  Local Definition min_n_UU : UU := ∑ n : nat, P n × minimal n.

  Local Definition isapropmin_n : isaprop min_n_UU.
  Proof.
    apply isaproptotal2.
    - intros n.
      apply isapropdirprod. apply (P n).
      apply isapropminimal.
    - intros n n' k k'.
      induction k as [p m], k' as [p' m'].
      apply isantisymmnatleh.
      + exact (m n' p').
      + exact (m' n p).
  Defined.

  Local Definition min_n : hProp := hProppair min_n_UU isapropmin_n.

  Local Definition smaller (n : nat) := ∑ l : nat, P l × minimal l × (l ≤ n)%nat.

  Local Definition smaller_S (n : nat) (k : smaller n) : smaller (S n).
  Proof.
    induction k as [l pmz].
    induction pmz as [p mz].
    induction mz as [m z].
    refine (l,,p,,m,,_).
    refine (istransnatgth _ _ _ _ _).
    apply natgthsnn.
    apply z.
  Defined.

  Local Definition bounded_search (n : nat) : smaller n ⨿ ∏ l : nat, (l ≤ n)%nat → ¬ P l.
  Proof.
    induction n.
    - assert (P 0 ⨿ ¬ P 0) as X.
      apply P_dec.
      induction X as [h|].
      + apply ii1.
        refine (O,,h,,_,,_).
        * intros ? ?. apply natleh0n.
        * apply isreflnatleh.
      + apply ii2. intros l lleq0.
        assert (l = O).
        apply natleh0tois0. assumption.
        rewrite H. assumption.
    - induction IHn as [|n0].
      + apply ii1. apply smaller_S. assumption.
      + assert (P (S n) ⨿ ¬ P (S n)) as X.
        apply P_dec.
        induction X as [h|].
        * refine (ii1 (S n,,h,,_,,_)).
          -- intros m q.
             assert (((S n) > m)%nat ⨿ (S n ≤ m)) as X.
             apply natgthorleh.
             induction X as [h0|].
             ++ apply fromempty.
                refine (n0 m h0 q).
             ++ assumption.
          -- apply isreflnatleh.
        * apply ii2. intros l q.
          assert ((l > n)%nat ⨿ (l ≤ n)) as X.
          apply natgthorleh.
          induction X as [h|h].
          -- assert (l = S n).
             apply isantisymmnatgeh. apply h. apply q. rewrite H. assumption.
          -- exact (n0 l h).
  Defined.


  Local Definition n_to_min_n (n : nat) (p : P n) : min_n.
  Proof.
    assert (smaller n ⨿ ∏ l : nat, (l ≤ n)%nat → ¬ P l) as X.
    apply bounded_search.
    induction X as [lqmz|none].
    - induction lqmz as [l qmz].
      induction qmz as [q mz].
      induction mz as [m z].
      refine (l,,q,,m).
    - apply fromempty.
      refine (none n (isreflnatgeh _ ) p).
  Defined.

  Local Definition prop_n_to_min_n : min_n.
  Proof.
    refine (@hinhuniv (∑ n : nat, P n) _ _ _).
    - induction 1 as [n p]. exact (n_to_min_n n p).
    - exact P_inhab.
  Defined.

  Definition minimal_n : ∑ n : nat, P n.
  Proof.
    induction prop_n_to_min_n as [n pl]. induction pl as [p _].
    exact (n,,p).
  Defined.

End constr_indef_descr.
