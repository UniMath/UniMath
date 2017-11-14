(** * Natural numbers and their properties. Vladimir Voevodsky. Apr. - Sep. 2011

This file contains the formulations and proofs of general properties of natural
numbers from the univalent perspecive. *)
(** ** Contents

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

Require Export UniMath.Foundations.NaturalNumbers.



(** ** Inductive types [le] with values in [UU].

This part is included for illustration purposes only. In practice it is easier
to work with [natleh] than with [le].

*)

(** *** A generalization of [le] and its properties. *)

Inductive leF {T : UU} (F : T -> T) (t : T) : T -> UU :=
| leF_O : leF F t t
| leF_S : ∏ t' : T, leF F t t' -> leF F t (F t').

Lemma leFiter {T : UU} (F : T -> T) (t : T) (n : nat) : leF F t (iteration F n t).
Proof.
  intros. induction n as [ | n IHn ].
  - apply leF_O.
  - simpl. unfold funcomp. apply leF_S. assumption.
Defined.

Lemma leFtototal2withnat {T : UU} (F : T -> T) (t t' : T) (a : leF F t t') :
  total2 (λ n : nat, (iteration F n t) = t').
Proof.
  intros. induction a as [ | b H0 IH0 ].
  - split with O. apply idpath.
  - split with (S (pr1 IH0)). simpl.
    apply (@maponpaths _ _ F (iteration F (pr1 IH0) t) b).
    apply (pr2 IH0).
Defined.

Lemma total2withnattoleF {T : UU} (F : T -> T) (t t' : T)
      (a : total2 (λ n : nat, (iteration F n t) = t')) : leF F t t'.
Proof.
  intros. destruct a as [ n e ]. destruct e. apply leFiter.
Defined.

Lemma leFtototal2withnat_l0 {T : UU} (F : T -> T) (t : T) (n : nat) :
  (leFtototal2withnat F t _ (leFiter F t n)) = (tpair _  n (idpath (iteration F n t))).
Proof.
  intros. induction n as [ | n IHn ].
  - apply idpath.
  - simpl.
    set (h := fun ne : total2 (λ n0 : nat, paths (iteration F n0 t) (iteration F n t)) =>
                tpair (λ n0 : nat, paths (iteration F n0 t) (iteration F (S n) t)) (S (pr1 ne))
                      (maponpaths F (pr2 ne))).
    apply (@maponpaths _ _ h  _ _ IHn).
Defined.

Lemma isweqleFtototal2withnat {T : UU} (F : T -> T) (t t' : T) : isweq (leFtototal2withnat F t t').
Proof.
  intros.
  set (f := leFtototal2withnat F t t').
  set (g := total2withnattoleF  F t t').
  assert (egf : ∏ x : _, paths (g (f x)) x).
  {
    intro x. induction x as [ | y H0 IHH0 ].
    - apply idpath.
    - simpl. simpl in IHH0.
      destruct (leFtototal2withnat F t y H0) as [ m e ].
      destruct e. simpl. simpl in IHH0.
      apply (@maponpaths _ _ (leF_S F t (iteration F m t)) _ _ IHH0).
  }
  assert (efg : ∏ x : _, paths (f (g x)) x).
  {
    intro x. destruct x as [ n e ]. destruct e. simpl.
    apply leFtototal2withnat_l0.
  }
  apply (gradth _ _ egf efg).
Defined.

Definition weqleFtototalwithnat { T : UU } (F : T -> T) (t t' : T) :
  weq (leF F t t') (total2 (λ n : nat, (iteration F n t) = t')) :=
  weqpair _ (isweqleFtototal2withnat F t t').


(** *** Inductive types [le] with values in [UU] are in [hProp] *)

Definition le (n : nat) : nat -> UU := leF S n.

Definition le_n : ∏ t : nat, leF S t t := leF_O S.

Definition le_S : ∏ t t' : nat, leF S t t' → leF S t (S t') := leF_S S.

Theorem isaprople (n m : nat) : isaprop (le n m).
Proof.
  intros.
  apply (isofhlevelweqb 1 (weqleFtototalwithnat S n m)).
  apply invproofirrelevance. intros x x'.
  set (i := @pr1 _ (λ n0 : nat, (iteration S n0 n) = m)).
  assert (is : isincl i) by apply (isinclpr1 _ (λ n0 : nat, isasetnat (iteration S n0 n) m)).
  apply (invmaponpathsincl _  is).
  destruct x as [ n1 e1 ]. destruct x' as [ n2 e2 ]. simpl.
  set (int1 := pathsinv0 (pathsitertoplus n1 n)).
  set (int2 := pathsinv0 (pathsitertoplus n2 n)).
  set (ee1 := pathscomp0 int1 e1).
  set (ee2 := pathscomp0 int2 e2).
  set (e := pathscomp0 ee1 (pathsinv0 ee2)).
  apply (invmaponpathsincl _ (isinclnatplusr n) n1 n2 e).
Defined.


(** *** Comparison between [le] with values in [UU] and [natleh]. *)

Lemma letoleh (n m : nat) : le n m -> n ≤ m.
Proof.
  intros n m H. induction H as [ | m H0 IHH0 ].
  - apply isreflnatleh.
  - apply natlehtolehs. assumption.
Defined.

Lemma natlehtole (n m : nat) : n ≤ m ->  le n m.
Proof.
  intros n m H. induction m as [|m IHm].
  - assert (int := natleh0tois0 H). clear H. destruct int. apply le_n.
  - set (int2 := natlehchoice2 n (S m) H).
    destruct int2 as [ isnatleh | iseq ].
    apply (le_S n m (IHm isnatleh)). destruct iseq.
    apply le_n.
Defined.

Lemma isweqletoleh (n m : nat) : isweq (letoleh n m).
Proof.
  intros.
  set (is1 := isaprople n m). set (is2 := pr2 (n ≤ m)).
  apply (isweqimplimpl (letoleh n m) (natlehtole n m) is1 is2).
Defined.

Definition weqletoleh (n m : nat) : le n m ≃ n ≤ m := weqpair _ (isweqletoleh n m).
