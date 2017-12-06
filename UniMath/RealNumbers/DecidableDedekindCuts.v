(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.RealNumbers.Prelim.
Require Import UniMath.RealNumbers.Sets.
Require Import UniMath.RealNumbers.NonnegativeRationals.
Require Export UniMath.RealNumbers.NonnegativeReals.

Unset Automatic Introduction.

Open Scope Dcuts_scope.

(** ** Definition *)

Lemma isboolDcuts_isaprop (x : Dcuts) :
  isaprop (∏ r, (r ∈ x) ∨ (neg (r ∈ x))).
Proof.
  intros x.
  apply impred_isaprop.
  intros r.
  apply pr2.
Qed.
Definition isboolDcuts : hsubtype Dcuts :=
  (λ x : Dcuts, hProppair _ (isboolDcuts_isaprop x)).

Lemma isaset_boolDcuts : isaset isboolDcuts.
Proof.
  apply isasetsubset with pr1.
  apply pr2.
  apply isinclpr1.
  intro x.
  apply pr2.
Qed.
Definition boolDcuts : hSet.
Proof.
  apply (hSetpair (carrier isboolDcuts)).
  exact isaset_boolDcuts.
Defined.
Definition mk_boolDcuts (x : Dcuts) (Hdec : ∏ r : NonnegativeRationals, (r ∈ x) ⨿ ¬ (r ∈ x)) : boolDcuts :=
  x,, (λ r : NonnegativeRationals, hinhpr (Hdec r)).

Lemma is_zero_dec :
  ∏ x : Dcuts, isboolDcuts x -> (x = 0) ∨ (¬ (x = 0)).
Proof.
  intros x Hx.
  generalize (Hx 0%NRat) ; apply hinhfun ; apply sumofmaps ; intros Hx0.
  - right ; intro H.
    rewrite H in Hx0.
    now apply Dcuts_zero_empty in Hx0.
  - left ; apply Dcuts_eq_is_eq.
    split.
    + intros Hr.
      apply fromempty.
      apply Hx0.
      apply (is_Dcuts_bot x r).
      now apply Hr.
      apply isnonnegative_NonnegativeRationals.
    + intros Hr.
      now apply Dcuts_zero_empty in Hr.
Qed.