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
  apply hnnq_nge_lt ; intro Hn'.
  apply Hr.  
  apply is_Dcuts_bot with n.
  exact Hn.
  exact Hn'.
Qed.

(** ** [Dcuts] is an ordered set *)
(** *** Large order and equality *)

(** [Dcuts_le] is a partial order on  *)

Definition Dcuts_le : hrel Dcuts :=
  fun (X Y : Dcuts) => ishinh (forall x : hnnq, pr1 X x -> pr1 Y x).
Lemma istrans_Dcuts_le : istrans Dcuts_le.
Proof.
  intros x y z.
  apply hinhfun2.
  intros Hxy Hyz r Xr.
  now apply Hyz, Hxy.
Qed.
Lemma isrefl_Dcuts_le : isrefl Dcuts_le.
Proof.
  now intros x P HP ; apply HP ; clear P HP.
Qed.

Definition Dcuts_le_po : po Dcuts.
Proof.
  exists  Dcuts_le.
  split.
  exact istrans_Dcuts_le.
  exact isrefl_Dcuts_le.
Defined.

(** [Dcuts_ge] is a partial order *)

Definition Dcuts_ge : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_le_po Y X.

Lemma istrans_Dcuts_ge : istrans Dcuts_ge.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_le with y.
Qed.
Lemma isrefl_Dcuts_ge : isrefl Dcuts_ge.
Proof.
  now apply isrefl_Dcuts_le.
Qed.
Definition Dcuts_ge_po : po Dcuts.
Proof.
  exists  Dcuts_ge.
  split.
  exact istrans_Dcuts_ge.
  exact isrefl_Dcuts_ge.
Defined.

(** [Dcuts_eq] is an equality *)

Definition Dcuts_eq : hrel Dcuts :=
  fun (X Y : Dcuts) => hconj (Dcuts_le_po X Y) (Dcuts_ge_po X Y).

Lemma istrans_Dcuts_eq : istrans Dcuts_eq.
Proof.
  intros x y z (Hxy,Hyx) (Hyz,Hzy).
  split.
  now apply istrans_Dcuts_le with y.
  now apply istrans_Dcuts_ge with y.
Qed.
Lemma isrefl_Dcuts_eq : isrefl Dcuts_eq.
Proof.
  intros x.
  split.
  now apply isrefl_Dcuts_le.
  now apply isrefl_Dcuts_ge.
Qed.
Lemma issymm_Dcuts_eq : issymm Dcuts_eq.
Proof.
  intros x y (Hxy,Hyx).
  now split.
Qed.

(** *** Strict order and appartness *)

(** [Dcuts_lt] is a strict partial order *)

Definition Dcuts_lt : hrel Dcuts :=
  fun (X Y : Dcuts) =>
    hexists (fun x : hnnq => dirprod (neg (pr1 X x)) (pr1 Y x)).
Lemma istrans_Dcuts_lt : istrans Dcuts_lt.
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
Lemma isirrefl_Dcuts_lt : isirrefl Dcuts_lt.
Proof.
  intros x.
  unfold neg ;
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (r,(nXr,Xr)).
  now apply nXr.
Qed.

(* to move in Sets.v *)
Definition isstpo {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition stpo (X : UU) := total2 (fun R : hrel X => isstpo R ).
Definition stpopair { X : UU } ( R : hrel X ) ( is : isstpo R ) : stpo X := tpair ( fun R : hrel X => isstpo R ) R is .
Definition carrierofstpo ( X : UU ) :  stpo X  -> ( X -> X -> hProp ) :=  @pr1 _ ( fun R : hrel X => isstpo R ) .
Coercion carrierofstpo : stpo >-> Funclass.
(* end *)

Definition Dcuts_lt_stpo : stpo Dcuts.
Proof.
  exists Dcuts_lt.
  split.
  exact istrans_Dcuts_lt.
  exact isirrefl_Dcuts_lt.
Defined.

(** [Dcuts_gt] is a strict partial order *)

Definition Dcuts_gt : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_lt_stpo Y X.
Lemma istrans_Dcuts_gt : istrans Dcuts_gt.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_lt with y.
Qed.
Lemma isirrefl_Dcuts_gt : isirrefl Dcuts_gt.
Proof.
  now apply isirrefl_Dcuts_lt.
Qed.

Definition Dcuts_gt_stpo : stpo Dcuts.
Proof.
  exists Dcuts_gt.
  split.
  exact istrans_Dcuts_gt.
  exact isirrefl_Dcuts_gt.
Defined.

(** [Dcuts_ap] is an apartness relation *)
(* todo : define apartness relation *)

Definition Dcuts_ap (X Y : Dcuts) : hProp :=
  hdisj (Dcuts_lt_stpo X Y) (Dcuts_gt_stpo X Y).

(** *** Various basic theorems about order, equality and apartness *)

Lemma Dcuts_lt_le :
  forall X Y : Dcuts, Dcuts_lt_stpo X Y -> Dcuts_le_po X Y.
Proof.
  intros X Y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply hnnq_lt_le.
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

(* to move to Sets.v *)

Definition isub {X : UU} (le : hrel X) (E : X -> hProp) (ub : X) :=
  forall x : X, E x -> le x ub.
Definition islbub {X : UU} (le : hrel X) (E : X -> hProp) (lub : X) :=
  forall ub : X, isub le E ub -> le lub ub.
Definition islub {X : UU} (le : hrel X) (E : X -> hProp) (lub : X) :=
  dirprod (isub le E lub) (islbub le E lub).
          
Definition lub {X : UU} (le : hrel X) (E : X -> hProp) :=
  total2 (islub le E).

Definition iscompleterel {X : UU} (le : hrel X) :=
  forall E : X -> hProp,
         hexists (fun M : X => forall x : X, E x -> le x M) -> hexists E -> lub le E.
Definition completerel (X : UU) :=
  total2 (fun le : hrel X => iscompleterel le).
Definition id_completerel {X : UU} : completerel X -> hrel X := pr1.
Coercion id_completerel : completerel >-> hrel.
(* end *)

Section Dcuts_lub.

Context (E : Dcuts -> hProp).
Context (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le_po x M)).

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
                     (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le_po x M)) : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_bounded E E_bounded).

Lemma isub_Dcuts_lub (E : Dcuts -> hProp)
      (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le_po x M)) :
  isub Dcuts_le_po E (Dcuts_lub E E_bounded).
Proof.
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r Hr.
  intros P HP ; apply HP ; clear P HP.
  now exists x.
Qed.
Lemma islbub_Dcuts_lub (E : Dcuts -> hProp)
      (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le_po x M)) :
  islbub Dcuts_le E (Dcuts_lub E E_bounded).
Proof.
  intros x Hx.  
  intros P HP ; apply HP ; clear P HP.
  intros r ; simpl.
  apply hinhuniv.
  intros (y,(Ey,Yr)).
  apply (Hx y Ey).
  now intros H ; apply H.
Qed.
Lemma islub_Dcuts_lub (E : Dcuts -> hProp)
      (E_bounded : hexists (fun M : Dcuts => forall x : Dcuts, E x -> Dcuts_le_po x M)) :
  islub Dcuts_le E (Dcuts_lub E E_bounded).
Proof.
  split.
  exact (isub_Dcuts_lub E E_bounded).
  exact (islbub_Dcuts_lub E E_bounded).
Qed.

(** * Notations and theorems *)

Delimit Scope Dcuts_scope with Dcuts.

(** [Dcuts] is an ordered set *)

Notation "x <= y" := (Dcuts_le x y) : Dcuts_scope.
Notation "x >= y" := (Dcuts_ge x y) : Dcuts_scope.
Notation "x < y" := (Dcuts_lt x y) : Dcuts_scope.
Notation "x > y" := (Dcuts_gt x y) : Dcuts_scope.

Close Scope hnnq.
Open Scope Dcuts.

Lemma Dcuts_ge_le :
  forall x y : Dcuts, x >= y -> y <= x.
Proof.
  easy.
Qed.
Lemma Dcuts_le_ge :
  forall x y : Dcuts, Dcuts_le x y -> Dcuts_ge y x.
Proof.
  easy.
Qed.

Lemma istrans_Dcuts_le_lt :
  forall x y z : Dcuts,
    Dcuts_le x y -> Dcuts_lt y z -> Dcuts_lt x z.
Proof.
Admitted.
Lemma istrans_Dcuts_lt_le :
  forall x y z : Dcuts,
    Dcuts_lt x y -> Dcuts_le y z -> Dcuts_lt x z.
Proof.
Admitted.

(** [iscomprelrel] *)

Lemma Dcuts_le_comp : iscomprelrel Dcuts_eq Dcuts_le.
Proof.
  apply iscomprelrelif.
  now apply issymm_Dcuts_eq.
  intros x x' y (Hx,Hx') Hxy.
  now eapply istrans_Dcuts_le, Hxy.
  intros x y y' (Hy,Hy') Hxy.
  now eapply istrans_Dcuts_le, Dcuts_ge_le, Hy.
Qed.
Lemma Dcuts_ge_comp : iscomprelrel Dcuts_eq Dcuts_ge.
Proof.
  apply iscomprelrelif.
  now apply issymm_Dcuts_eq.
  intros x x' y (Hx,Hx') Hxy.
  now eapply istrans_Dcuts_ge, Hxy.
  intros x y y' (Hy,Hy') Hxy.
  now eapply istrans_Dcuts_ge, Hy'.
Qed.
Lemma Dcuts_lt_comp : iscomprelrel Dcuts_eq Dcuts_lt.
Proof.
  apply iscomprelrelif.
  now apply issymm_Dcuts_eq.
  intros x x' y (Hx,Hx') Hxy.
  now eapply istrans_Dcuts_le_lt, Hxy.
  intros x y y' (Hy,Hy') Hxy.
  now eapply istrans_Dcuts_lt_le, Dcuts_ge_le, Hy.
Qed.

(** Opaque functions and relations *)

Global Opaque Dcuts_eq Dcuts_le Dcuts_ge.
Global Opaque Dcuts_ap Dcuts_lt Dcuts_gt.

(* End of the file Dcuts.v *)

