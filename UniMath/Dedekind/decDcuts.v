(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.DedekindCuts.

(** ** Definition *)

Definition isdecDcuts : hsubtypes Dcuts :=
  (fun x : Dcuts => ishinh (forall r, coprod (r ∈ x) (neg (r ∈ x)))).

(* Definition decDcuts : hSet.
Proof.
  apply (hSetpair (carrier isdecDcuts)).
  apply isasetsubset with pr1.
  apply pr2.
  apply isinclpr1.
  intro x.
  apply pr2.
Defined.
Definition mk_decDcuts (x : Dcuts) (Hdec : forall r, coprod (r ∈ x) (neg (r ∈ x))) : decDcuts.
Proof.
  exists x.
  now apply hinhpr.
Defined. *)
  
(** ** Cotransitivity *)

Lemma iscotrans_Dcuts_lt :
  forall x y z : Dcuts,
    Dcuts_lt x z -> isdecDcuts y ->
      hdisj (Dcuts_lt x y) (Dcuts_lt y z).
Proof.
  intros x y z.
  apply hinhfun2.
  intros (r,(Xr,Zr)) Hy.
  generalize (Hy r) ; clear Hy ; intros [Yr | Yr].
  left.
  intros P HP ; apply HP ; clear P HP.
  now exists r ; split.
  right.
  intros P HP ; apply HP ; clear P HP.
  now exists r ; split.
Qed.

Lemma iscotrans_Dcuts_gt :
  forall x y z : Dcuts,
    Dcuts_gt x z -> isdecDcuts y ->
      hdisj (Dcuts_gt x y) (Dcuts_gt y z).
Proof.
  intros.
  apply islogeqcommhdisj.
  now apply iscotrans_Dcuts_lt.
Qed.

Lemma iscotrans_Dcuts_ap :
  forall x y z : Dcuts,
    Dcuts_ap x z -> isdecDcuts y ->
      hdisj (Dcuts_ap x y) (Dcuts_ap y z).
Proof.
  intros x y z Hxz Hy.
  revert Hxz ; apply hinhuniv ; intros [Hxz | Hxz].
  - apply iscotrans_Dcuts_lt with x y z in Hy.
    2: exact Hxz.
    revert Hy ; apply hinhfun ; intros [Hy | Hy].
    + left.
      intros P HP ; apply HP ; clear HP.
      now left.
    + right.
      intros P HP ; apply HP ; clear HP.
      now left.
  - apply iscotrans_Dcuts_gt with x y z in Hy.
    2: exact Hxz.
    revert Hy ; apply hinhfun ; intros [Hy | Hy].
    + left.
      intros P HP ; apply HP ; clear HP.
      now right.
    + right.
      intros P HP ; apply HP ; clear HP.
      now right.
Qed.