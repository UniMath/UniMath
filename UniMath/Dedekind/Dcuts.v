(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.hnnq.

Local Open Scope hnnq_scope.

(** ** Non-negative real numbers *)
(** Definition *)

Definition Dcuts_def_bot (X : hnnq -> hProp) : hProp :=
  ishinh (forall x : hnnq, X x ->
    forall y : hnnq, y <= x -> X y).
Definition Dcuts_def_open (X : hnnq -> hProp) : hProp :=
  ishinh (forall x : hnnq, X x ->
    hexists (fun y : hnnq => dirprod (X y) (x < y))).
Definition Dcuts_def_bounded (X : hnnq -> hProp) : hProp :=
  hexists (fun ub : hnnq => neg (X ub)).

Definition Dcuts : hsubtypes (hnnq -> hProp) :=
  (fun X : hnnq -> hProp => hconj (Dcuts_def_bot X)
                           (hconj (Dcuts_def_open X)
                                  (Dcuts_def_bounded X))).

Lemma is_Dcuts_bot (X : Dcuts) :
  forall x : hnnq, pr1 X x ->
    forall y : hnnq, y <= x -> pr1 X y.
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr y Hxy.
  revert Hbot ; apply hinhuniv ; intros Hbot.
  now apply Hbot with r.
Qed.
Lemma is_Dcuts_open (X : Dcuts) :
  forall x : hnnq, pr1 X x ->
    hexists (fun y : hnnq => dirprod (pr1 X y) (x < y)).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr.
  revert Hopen ; apply (hinhuniv (P := ishinh _)) ; intros Hopen.
  now apply Hopen.
Qed.
Lemma is_Dcuts_bounded (X : Dcuts) :
  hexists (fun ub : hnnq => neg (pr1 X ub)).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  now apply Hbound.
Qed.

Definition mk_Dcuts (X : hnnq -> hProp)
                   (Hbot : forall x : hnnq, X x ->
                     forall y : hnnq, y <= x -> X y)
                   (Hopen : forall x : hnnq, X x ->
                     hexists (fun y : hnnq => dirprod (X y) (x < y)))
                   (Hbound : hexists (fun ub : hnnq => neg (X ub))) : Dcuts.
Proof.
  exists X ; repeat split.
  intros P HP ; apply HP.
  exact Hbot.
  intros P HP ; apply HP.
  exact Hopen.
  exact Hbound.
Defined.

Lemma Dcuts_bounded :
  forall X : Dcuts, forall r : hnnq,
    neg (pr1 X r) -> forall n : hnnq, pr1 X n -> n < r.
Proof.
  intros X r Hr n Hn.
  apply neghqgehtolth ; intro Hn'.
  apply Hr.  
  apply is_Dcuts_bot with n.
  exact Hn.
  exact Hn'.
Qed.

(** ** [Dcuts] is an ordered set *)
(** *** Large order and equality *)

(** [Dcuts_le] is a partial order on  *)

Definition Dcuts_le_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => ishinh (forall x : hnnq, pr1 X x -> pr1 Y x).
Lemma istrans_Dcuts_le_rel : istrans Dcuts_le_rel.
Proof.
  intros x y z.
  apply hinhfun2.
  intros Hxy Hyz r Xr.
  now apply Hyz, Hxy.
Qed.
Lemma isrefl_Dcuts_le_rel : isrefl Dcuts_le_rel.
Proof.
  now intros x P HP ; apply HP ; clear P HP.
Qed.

Definition Dcuts_le : po Dcuts.
Proof.
  exists  Dcuts_le_rel.
  split.
  exact istrans_Dcuts_le_rel.
  exact isrefl_Dcuts_le_rel.
Defined.
Lemma istrans_Dcuts_le : istrans Dcuts_le.
Proof.
  apply istrans_Dcuts_le_rel.
Qed.
Lemma isrefl_Dcuts_le : isrefl Dcuts_le.
Proof.
  apply isrefl_Dcuts_le_rel.
Qed.

(** [Dcuts_ge] is a partial order *)

Definition Dcuts_ge_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_le Y X.

Lemma istrans_Dcuts_ge_rel : istrans Dcuts_ge_rel.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_le_rel with y.
Qed.
Lemma isrefl_Dcuts_ge_rel : isrefl Dcuts_ge_rel.
Proof.
  now apply isrefl_Dcuts_le_rel.
Qed.
Definition Dcuts_ge : po Dcuts.
Proof.
  exists  Dcuts_ge_rel.
  split.
  exact istrans_Dcuts_ge_rel.
  exact isrefl_Dcuts_ge_rel.
Defined.

(** [Dcuts_eq] is an equality *)

Definition Dcuts_eq_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => hconj (Dcuts_le X Y) (Dcuts_ge X Y).

Lemma istrans_Dcuts_eq_rel : istrans Dcuts_eq_rel.
Proof.
  intros x y z (Hxy,Hyx) (Hyz,Hzy).
  split.
  now apply istrans_Dcuts_le_rel with y.
  now apply istrans_Dcuts_ge_rel with y.
Qed.
Lemma isrefl_Dcuts_eq_rel : isrefl Dcuts_eq_rel.
Proof.
  intros x.
  split.
  now apply isrefl_Dcuts_le_rel.
  now apply isrefl_Dcuts_ge_rel.
Qed.
Lemma issymm_Dcuts_eq_rel : issymm Dcuts_eq_rel.
Proof.
  intros x y (Hxy,Hyx).
  now split.
Qed.
Definition Dcuts_eq : eqrel Dcuts.
Proof.
  exists Dcuts_eq_rel.
  split ; [split | ].
  exact istrans_Dcuts_eq_rel.
  exact isrefl_Dcuts_eq_rel.
  exact issymm_Dcuts_eq_rel.
Defined.

(** *** Strict order and appartness *)

(** [Dcuts_lt] is a strict partial order *)

Definition Dcuts_lt_rel : hrel Dcuts :=
  fun (X Y : Dcuts) =>
    hexists (fun x : hnnq => dirprod (neg (pr1 X x)) (pr1 Y x)).
Lemma istrans_Dcuts_lt_rel : istrans Dcuts_lt_rel.
Proof.
  intros x y z.
  apply hinhfun2.
  intros (r,(Xr,Yr)) (n,(Yn,Zn)).
  exists r ; split.
  exact Xr.
  apply is_Dcuts_bot with n.
  exact Zn.
  apply hnnq_lt_le.
  now apply Dcuts_bounded with y.
Qed.
Lemma isirrefl_Dcuts_lt_rel : isirrefl Dcuts_lt_rel.
Proof.
  intros x.
  unfold neg ;
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (r,(nXr,Xr)).
  now apply nXr.
Qed.

(* to move *)
Definition isstpo {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition stpo (X : UU) := total2 (fun R : hrel X => isstpo R ).
Definition stpopair { X : UU } ( R : hrel X ) ( is : isstpo R ) : stpo X := tpair ( fun R : hrel X => isstpo R ) R is .
Definition carrierofstpo ( X : UU ) :  stpo X  -> ( X -> X -> hProp ) :=  @pr1 _ ( fun R : hrel X => isstpo R ) .
Coercion carrierofstpo : stpo >-> Funclass.
(* end *)

Definition Dcuts_lt : stpo Dcuts.
Proof.
  exists Dcuts_lt_rel.
  split.
  exact istrans_Dcuts_lt_rel.
  exact isirrefl_Dcuts_lt_rel.
Defined.

(** [Dcuts_gt] is a struct partial order *)

Definition Dcuts_gt_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_lt Y X.
Lemma istrans_Dcuts_gt_rel : istrans Dcuts_gt_rel.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_lt_rel with y.
Qed.
Lemma isirrefl_Dcuts_gt_rel : isirrefl Dcuts_gt_rel.
Proof.
  now apply isirrefl_Dcuts_lt_rel.
Qed.

Definition Dcuts_gt : stpo Dcuts.
Proof.
  exists Dcuts_gt_rel.
  split.
  exact istrans_Dcuts_gt_rel.
  exact isirrefl_Dcuts_gt_rel.
Defined.

(** [Dcuts_ap] is an appartness relation *)

Definition Dcuts_ap (X Y : Dcuts) : hProp :=
  hdisj (Dcuts_lt X Y) (Dcuts_gt X Y).

(** *** Various Theorems *)

Lemma hhnr_lt_le :
  forall X Y : Dcuts, Dcuts_lt X Y -> Dcuts_le X Y.
Proof.
  intros X Y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply hqlthtoleh.
  now apply Dcuts_bounded with X.
Qed.

(* Lemma Dcuts_le_ngt :
  forall X Y, Dcuts_le X Y -> neg (Dcuts_gt X Y).
Proof.
  intros X Y Hxy (r,(Yr,Xr)).
  now apply Yr, Hxy.
Qed.
Lemma Dcuts_gt_nle :
  forall X Y, Dcuts_gt X Y -> neg (Dcuts_le X Y).
Proof.
  intros X Y (r,(Yr,Xr)) Hyx.
  now apply Yr, Hyx.
Qed.

Lemma Dcuts_ge_nlt :
  forall X Y, Dcuts_ge X Y -> neg (Dcuts_lt X Y).
Proof.
  intros X Y.
  now apply Dcuts_le_ngt.
Qed.
Lemma Dcuts_lt_nge :
  forall X Y, Dcuts_lt X Y -> neg (Dcuts_ge X Y).
Proof.
  intros X Y (r,(Yr,Xr)) Hyx.
  now apply Yr, Hyx.
Qed.

Lemma Dcuts_eq_nap :
  forall X Y, Dcuts_eq X Y -> neg (Dcuts_ap X Y).
Proof.
  intros X Y [Hxy Hyx] Hap.
  destruct Hap as [Hap|Hap].
  now apply Dcuts_ge_nlt in Hyx.
  now apply Dcuts_le_ngt in Hxy.
Qed.
Lemma Dcuts_nap_eq :
  forall X Y, neg (Dcuts_ap X Y) -> Dcuts_eq X Y.
Proof.
  intros X Y Hap ; split ; intros r Hr.
  
Qed.

(** *** Strict order and appartness *)
(** irreflexive *)

Lemma Dcuts_lt_irrefl :
  forall X, neg (Dcuts_lt X X).
Proof.
  intros X (x,(Hnx,Hx)).
  now apply Hnx, Hx.
Qed.
Lemma Dcuts_gt_irrefl :
  forall X, neg (Dcuts_gt X X).
Proof.
  now apply Dcuts_lt_irrefl.
Qed.
Lemma Dcuts_ap_irrefl :
  forall X, neg (Dcuts_ap X X).
Proof.
  intros X [H|H].
  now apply Dcuts_lt_irrefl with (1 := H).
  now apply Dcuts_lt_irrefl with (1 := H).
Qed.

(** cotransitivity *)

Lemma  Dcuts_lt_cotrans :
  forall X Y, Dcuts_lt X Y ->
    forall Z, coprod (Dcuts_lt X Z) (Dcuts_lt Z Y).
Proof.
  intros X Y (r,(Xr,Yr)) Z.

Search bool.
Qed.

Lemma Dcuts_ap_cotrans :
  forall X Y,
    Dcuts_ap X Y -> forall Z, coprod (Dcuts_ap X Z) (Dcuts_ap Z Y).
Lemma Dcuts_ap_cotrans :
  forall X Y,
    Dcuts_ap X Y -> forall Z, coprod (Dcuts_ap X Z) (Dcuts_ap Z Y).

(** *** Large order and equivalence *) *)

(** ** Least Upper Bound *)

Section Dcuts_lub.

Context (E : Dcuts -> hProp).
Context (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le x M)).

Definition Dcuts_lub_val : hnnq -> hProp :=
  fun r : hnnq => hexists (fun X : Dcuts => dirprod (E X) (pr1 X r)).
Lemma Dcuts_lub_bot : 
  forall (x : hnnq),
    Dcuts_lub_val x -> forall y : hnnq, y <= x -> Dcuts_lub_val y.
Proof.
  intros r Xr n Xn.
  revert Xr ; apply hinhfun ; intros (X,(Ex,Xr)).
  exists X ; split.
  exact Ex.
  now apply is_Dcuts_bot with r.
Qed.
Lemma Dcuts_lub_open :
  forall (x : hnnq),
    Dcuts_lub_val x ->
    hexists (fun y : hnnq => dirprod (Dcuts_lub_val y) (x < y)).
Proof.
  intros r.
  apply hinhuniv ; intros (X,(Ex,Xr)).
  generalize (is_Dcuts_open X r Xr). 
  apply hinhfun ; intros (n,(Xn,Hrn)).
  exists n ; split.
  intros P HP ; apply HP ; clear P HP.
  exists X ; split.
  exact Ex.
  exact Xn.
  exact Hrn.
Qed.
Lemma Dcuts_lub_bounded :
   hexists (fun ub : hnnq => neg (Dcuts_lub_val ub)).
Proof.
  revert E_bounded.
  apply hinhuniv.
  intros (M,HM).
  generalize (is_Dcuts_bounded M).
  apply hinhfun.
  intros (ub,Hub).
  exists ub.
  unfold neg.
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (x,(Ex,Hx)).
  apply Hub.
  generalize (HM x Ex).
  apply hinhuniv ; intro H.
  now apply H.
Qed.

End Dcuts_lub.

Definition Dcuts_lub (E : Dcuts -> hProp)
                    (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le x M)) : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_bounded E E_bounded).



(* End of the file Dcuts.v *)

