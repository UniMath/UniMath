(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.hnnq.

Local Open Scope hnnq_scope.

(** ** Non-negative real numbers *)
(** Definition *)
 
Definition hnnr_def_bot (X : hnnq -> hProp) : hProp :=
  ishinh (forall x : hnnq, X x ->
    forall y : hnnq, y <= x -> X y).
Definition hnnr_def_open (X : hnnq -> hProp) : hProp :=
  ishinh (forall x : hnnq, X x ->
    hexists (fun y : hnnq => dirprod (X y) (x < y))).
Definition hnnr_def_bounded (X : hnnq -> hProp) : hProp :=
  hexists (fun ub : hnnq => neg (X ub)).

Definition hnnr_def :=
  total2 (fun X : hnnq -> hProp => hconj (hnnr_def_bot X)
                                  (hconj (hnnr_def_open X)
                                         (hnnr_def_bounded X))).

Lemma is_hnnr_bot (X : hnnr_def) :
  forall x : hnnq, pr1 X x ->
    forall y : hnnq, y <= x -> pr1 X y.
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr y Hxy.
  revert Hbot ; apply hinhuniv ; intros Hbot.
  now apply Hbot with r.
Qed.
Lemma is_hnnr_open (X : hnnr_def) :
  forall x : hnnq, pr1 X x ->
    hexists (fun y : hnnq => dirprod (pr1 X y) (x < y)).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr.
  revert Hopen ; apply (hinhuniv (P := ishinh _)) ; intros Hopen.
  now apply Hopen.
Qed.
Lemma is_hnnr_bounded (X : hnnr_def) :
  hexists (fun ub : hnnq => neg (pr1 X ub)).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  now apply Hbound.
Qed.

Definition mk_hnnr_def (X : hnnq -> hProp)
                   (Hbot : forall x : hnnq, X x ->
                     forall y : hnnq, y <= x -> X y)
                   (Hopen : forall x : hnnq, X x ->
                     hexists (fun y : hnnq => dirprod (X y) (x < y)))
                   (Hbound : hexists (fun ub : hnnq => neg (X ub))) : hnnr_def.
Proof.
  exists X ; repeat split.
  intros P HP ; apply HP.
  exact Hbot.
  intros P HP ; apply HP.
  exact Hopen.
  exact Hbound.
Defined.

Lemma hnnr_bounded :
  forall X : hnnr_def, forall r : hnnq,
    neg (pr1 X r) -> forall n : hnnq, pr1 X n -> n < r.
Proof.
  intros X r Hr n Hn.
  apply neghqgehtolth ; intro Hn'.
  apply Hr.  
  apply is_hnnr_bot with n.
  exact Hn.
  exact Hn'.
Qed.

(** ** [hnnr] is an ordered set *)
(** *** Large order and equality *)

(** [hnnr_le] is a partial order *)

Definition hnnr_le_rel : hrel hnnr_def :=
  fun (X Y : hnnr_def) => ishinh (forall x : hnnq, pr1 X x -> pr1 Y x).

Lemma istrans_hnnr_le_rel : istrans hnnr_le_rel.
Proof.
  intros x y z.
  apply hinhfun2.
  intros Hxy Hyz r Xr.
  now apply Hyz, Hxy.
Qed.
Lemma isrefl_hnnr_le_rel : isrefl hnnr_le_rel.
Proof.
  now intros x P HP ; apply HP ; clear P HP.
Qed.
Definition hnnr_le : po hnnr_def.
Proof.
  exists  hnnr_le_rel.
  split.
  exact istrans_hnnr_le_rel.
  exact isrefl_hnnr_le_rel.
Defined.

(** [hnnr_ge] is a partial order *)

Definition hnnr_ge_rel : hrel hnnr_def :=
  fun (X Y : hnnr_def) => hnnr_le Y X.

Lemma istrans_hnnr_ge_rel : istrans hnnr_ge_rel.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_hnnr_le_rel with y.
Qed.
Lemma isrefl_hnnr_ge_rel : isrefl hnnr_ge_rel.
Proof.
  now apply isrefl_hnnr_le_rel.
Qed.
Definition hnnr_ge : po hnnr_def.
Proof.
  exists  hnnr_ge_rel.
  split.
  exact istrans_hnnr_ge_rel.
  exact isrefl_hnnr_ge_rel.
Defined.

(** [hnnr_eq] is an equality *)

Definition hnnr_eq_rel : hrel hnnr_def :=
  fun (X Y : hnnr_def) => hconj (hnnr_le_rel X Y) (hnnr_ge_rel X Y).

Lemma istrans_hnnr_eq_rel : istrans hnnr_eq_rel.
Proof.
  intros x y z (Hxy,Hyx) (Hyz,Hzy).
  split.
  now apply istrans_hnnr_le_rel with y.
  now apply istrans_hnnr_ge_rel with y.
Qed.
Lemma isrefl_hnnr_eq_rel : isrefl hnnr_eq_rel.
Proof.
  intros x.
  split.
  now apply isrefl_hnnr_le_rel.
  now apply isrefl_hnnr_ge_rel.
Qed.
Lemma issymm_hnnr_eq_rel : issymm hnnr_eq_rel.
Proof.
  intros x y (Hxy,Hyx).
  now split.
Qed.
Definition hnnr_eq : eqrel hnnr_def.
Proof.
  exists hnnr_eq_rel.
  split ; [split | ].
  exact istrans_hnnr_eq_rel.
  exact isrefl_hnnr_eq_rel.
  exact issymm_hnnr_eq_rel.
Defined.

Definition hnnr_set : hSet := setquotinset hnnr_eq.

(** *** Strict order and appartness *)

(** [hnnr_lt] is a partial order *)

Definition hnnr_lt (X Y : hnnr_def) : hProp :=
  hexists (fun x : hnnq => dirprod (neg (pr1 X x)) (pr1 Y x)).

(** [hnnr_gt] is a partial order *)

Definition hnnr_gt (X Y : hnnr_def) : hProp :=
  hnnr_lt Y X.

(** [hnnr_ap] is an appartness relation *)

Definition hnnr_ap (X Y : hnnr_def) : hProp :=
  hdisj (hnnr_lt X Y) (hnnr_gt X Y).

(** *** Various Theorems *)

Lemma hhnr_lt_le :
  forall X Y : hnnr_def, hnnr_lt X Y -> hnnr_le X Y.
Proof.
  intros X Y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_hnnr_bot with r.
  exact Yr.
  apply hqlthtoleh.
  now apply hnnr_bounded with X.
Qed.

(* Lemma hnnr_le_ngt :
  forall X Y, hnnr_le X Y -> neg (hnnr_gt X Y).
Proof.
  intros X Y Hxy (r,(Yr,Xr)).
  now apply Yr, Hxy.
Qed.
Lemma hnnr_gt_nle :
  forall X Y, hnnr_gt X Y -> neg (hnnr_le X Y).
Proof.
  intros X Y (r,(Yr,Xr)) Hyx.
  now apply Yr, Hyx.
Qed.

Lemma hnnr_ge_nlt :
  forall X Y, hnnr_ge X Y -> neg (hnnr_lt X Y).
Proof.
  intros X Y.
  now apply hnnr_le_ngt.
Qed.
Lemma hnnr_lt_nge :
  forall X Y, hnnr_lt X Y -> neg (hnnr_ge X Y).
Proof.
  intros X Y (r,(Yr,Xr)) Hyx.
  now apply Yr, Hyx.
Qed.

Lemma hnnr_eq_nap :
  forall X Y, hnnr_eq X Y -> neg (hnnr_ap X Y).
Proof.
  intros X Y [Hxy Hyx] Hap.
  destruct Hap as [Hap|Hap].
  now apply hnnr_ge_nlt in Hyx.
  now apply hnnr_le_ngt in Hxy.
Qed.
Lemma hnnr_nap_eq :
  forall X Y, neg (hnnr_ap X Y) -> hnnr_eq X Y.
Proof.
  intros X Y Hap ; split ; intros r Hr.
  
Qed.

(** *** Strict order and appartness *)
(** irreflexive *)

Lemma hnnr_lt_irrefl :
  forall X, neg (hnnr_lt X X).
Proof.
  intros X (x,(Hnx,Hx)).
  now apply Hnx, Hx.
Qed.
Lemma hnnr_gt_irrefl :
  forall X, neg (hnnr_gt X X).
Proof.
  now apply hnnr_lt_irrefl.
Qed.
Lemma hnnr_ap_irrefl :
  forall X, neg (hnnr_ap X X).
Proof.
  intros X [H|H].
  now apply hnnr_lt_irrefl with (1 := H).
  now apply hnnr_lt_irrefl with (1 := H).
Qed.

(** cotransitivity *)

Lemma  hnnr_lt_cotrans :
  forall X Y, hnnr_lt X Y ->
    forall Z, coprod (hnnr_lt X Z) (hnnr_lt Z Y).
Proof.
  intros X Y (r,(Xr,Yr)) Z.

Search bool.
Qed.

Lemma hnnr_ap_cotrans :
  forall X Y,
    hnnr_ap X Y -> forall Z, coprod (hnnr_ap X Z) (hnnr_ap Z Y).
Lemma hnnr_ap_cotrans :
  forall X Y,
    hnnr_ap X Y -> forall Z, coprod (hnnr_ap X Z) (hnnr_ap Z Y).

(** *** Large order and equivalence *) *)

(** ** Least Upper Bound *)

Definition hnnr_lub_val (E : hnnr_def -> hProp) : hnnq -> hProp :=
  fun r : hnnq => hexists (fun X : hnnr_def => dirprod (E X) (pr1 X r)).
Lemma hnnr_lub_bot (E : hnnr_def -> hProp) : 
  forall (x : hnnq),
    hnnr_lub_val E x -> forall y : hnnq, y <= x -> hnnr_lub_val E y.
Proof.
  intros r Xr n Xn.
  revert Xr ; apply hinhfun ; intros (X,(Ex,Xr)).
  exists X ; split.
  exact Ex.
  now apply is_hnnr_bot with r.
Qed.
Lemma hnnr_lub_open (E : hnnr_def -> hProp) :
  forall (x : hnnq),
    hnnr_lub_val E x ->
    hexists (fun y : hnnq => dirprod (hnnr_lub_val E y) (x < y)).
Proof.
  intros r.
  apply hinhuniv ; intros (X,(Ex,Xr)).
  generalize (is_hnnr_open X r Xr). 
  apply hinhfun ; intros (n,(Xn,Hrn)).
  exists n ; split.
  intros P HP ; apply HP ; clear P HP.
  exists X ; split.
  exact Ex.
  exact Xn.
  exact Hrn.
Qed.
Lemma hnnr_lub_bounded (E : hnnr_def -> hProp) :
   hexists (fun ub : hnnq => neg (hnnr_lub_val E ub)).
Proof.
  (* Need order *)
Admitted.

Definition hnnr_lub  (E : hnnr_def -> hProp) : hnnr_def :=
  mk_hnnr_def (hnnr_lub_val E) (hnnr_lub_bot E) (hnnr_lub_open E) (hnnr_lub_bounded E).

(* End of the file hnnr.v *)

