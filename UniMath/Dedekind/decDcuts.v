(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.DedekindCuts.

Open Scope Dcuts_scope.

(** ** Definition *)

Lemma isdecDcuts_isaprop (x : Dcuts) :
  isaprop (forall r, hdisj (r ∈ x) (neg (r ∈ x))).
Proof.
  intros x.
  apply impred_isaprop.
  intros r.
  apply pr2.
Qed.
Definition isdecDcuts : hsubtypes Dcuts :=
  (fun x : Dcuts => hProppair _ (isdecDcuts_isaprop x)).

Lemma isaset_decDcuts : isaset isdecDcuts.
Proof.
  apply isasetsubset with pr1.
  apply pr2.
  apply isinclpr1.
  intro x.
  apply pr2.
Qed.
Definition decDcuts : hSet.
Proof.
  apply (hSetpair (carrier isdecDcuts)).
  exact isaset_decDcuts.
Defined.
Definition mk_decDcuts (x : Dcuts) (Hdec : forall r, coprod (r ∈ x) (neg (r ∈ x))) : decDcuts :=
  tpair (fun x0 : Dcuts => isdecDcuts x0) x (fun r => hinhpr _ (Hdec r)).

Lemma is_zero_dec :
  forall x : Dcuts, isdecDcuts x -> hdisj (x = 0) (neg (x = 0)).
Proof.
  intros x Hx.
  generalize (Hx 0%NRat) ; apply hinhfun ; intros [Hx0 | Hx0].
  - right ; intro H.
    rewrite H in Hx0.
    now rewrite Dcuts_zero_empty in Hx0.
  - left ; apply Dcuts_eq_is_eq.
    intros P HP ; apply HP ; clear P HP.
    split.
    + intros Hr.
      rewrite Dcuts_zero_empty.
      apply Hx0.
      apply (is_Dcuts_bot x r).
      now apply Hr.
      apply isnonnegative_NonnegativeRationals.
    + intros Hr.
      now rewrite Dcuts_zero_empty in Hr.
Qed.
  
(** ** Cotransitivity *)

Lemma iscotrans_Dcuts_lt :
  forall x y z : Dcuts, isdecDcuts y ->
    x < z -> hdisj (x < y) (y < z).
Proof.
  intros x y z Hy.
  apply hinhuniv.
  intros (r,(Xr,Zr)).
  generalize (Hy r) ; clear Hy.
  apply hinhfun ; intros [Hy | Hy].
  - left.
    apply hinhpr.
    now exists r ; split.
  - right.
    apply hinhpr.
    now exists r ; split.
Qed.

Lemma iscotrans_Dcuts_gt :
  forall x y z : Dcuts, isdecDcuts y ->
    x > z -> hdisj (x > y) (y > z).
Proof.
  intros.
  apply islogeqcommhdisj.
  now apply iscotrans_Dcuts_lt.
Qed.

Lemma iscotrans_Dcuts_ap :
  forall x y z : Dcuts, isdecDcuts y ->
    Dcuts_ap x z -> hdisj (Dcuts_ap x y) (Dcuts_ap y z).
Proof.
  intros x y z Hy Hxz.
  revert Hxz ; apply hinhuniv ; intros [Hxz | Hxz].
  - apply iscotrans_Dcuts_lt with x y z in Hxz.
    2: exact Hy.
    revert Hxz ; apply hinhfun ; intros [Hxz | Hxz].
    + left ; apply hinhpr.
      now left.
    + right ; apply hinhpr.
      now left.
  - apply iscotrans_Dcuts_gt with x y z in Hxz.
    2: exact Hy.
    revert Hxz ; apply hinhfun ; intros [Hxz | Hxz].
    + left ; apply hinhpr.
      now right.
    + right ; apply hinhpr.
      now right.
Qed.