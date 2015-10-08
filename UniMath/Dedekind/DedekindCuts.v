(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Import UniMath.Foundations.FunctionalExtensionality.

Open Scope NnR_scope.

(** ** Definition of Dedekind cuts *)

Definition Dcuts_def_bot (X : subset NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    forall y : NonnegativeRationals, y <= x -> X y.
Definition Dcuts_def_open (X : subset NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)).
Definition Dcuts_def_bounded (X : subset NonnegativeRationals) : hProp :=
  hexists (fun ub : NonnegativeRationals => neg (X ub)).

Definition Dcuts_hsubtypes : hsubtypes (subset NonnegativeRationals) :=
  fun X : subset NonnegativeRationals => hconj (ishinh (Dcuts_def_bot X))
                                               (hconj (ishinh (Dcuts_def_open X))
                                                      (Dcuts_def_bounded X)).
Lemma isaset_Dcuts : isaset (carrier Dcuts_hsubtypes).
Proof.
  apply isasetsubset with pr1.
  apply pr2.
  apply isinclpr1.
  intro x.
  apply pr2.
Qed.
Definition Dcuts : hSet := hSetpair _ isaset_Dcuts.
Definition pr1Dcuts (x : Dcuts) : subset NonnegativeRationals := pr1 x.
Notation "x ∈ X" := (pr1Dcuts X x) (at level 70, no associativity) : DC_scope.

Open Scope DC_scope.

Lemma is_Dcuts_bot (X : Dcuts) : Dcuts_def_bot (pr1 X).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr y Hxy.
  revert Hbot ; apply hinhuniv ; intros Hbot.
  now apply Hbot with r.
Qed.
Lemma is_Dcuts_open (X : Dcuts) : Dcuts_def_open (pr1 X).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  intros r Xr.
  revert Hopen ; apply (hinhuniv (P := ishinh _)) ; intros Hopen.
  now apply Hopen.
Qed.

Lemma is_Dcuts_bounded (X : Dcuts) :
  hexists (fun ub : NonnegativeRationals => neg (ub ∈ X)).
Proof.
  destruct X as [X (Hbot,(Hopen,Hbound))] ; simpl.
  now apply Hbound.
Qed.

Definition mk_Dcuts (X : NonnegativeRationals -> hProp)
                    (Hbot : Dcuts_def_bot X)
                    (Hopen : Dcuts_def_open X)
                    (Hbound : Dcuts_def_bounded X) : Dcuts.
Proof.
  intros X Hbot Hopen Hbound.
  exists X ; repeat split.
  now apply hinhpr.
  now apply hinhpr.
  exact Hbound.
Defined.

Lemma Dcuts_bounded :
  forall X : Dcuts, forall r : NonnegativeRationals,
    neg (r ∈ X) -> forall n : NonnegativeRationals, n ∈ X -> n < r.
Proof.
  intros X r Hr n Hn.
  apply notge_ltNonnegativeRationals ; intro Hn'.
  apply Hr.  
  apply is_Dcuts_bot with n.
  exact Hn.
  exact Hn'.
Qed.

(** ** [Dcuts] is an ordered set *)
(** *** Large orders and alternative definition of equality *)

(** [Dcuts_le] is a partial order on [Dcuts] *)

Definition Dcuts_le_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => ishinh (forall x : NonnegativeRationals, x ∈ X -> x ∈ Y).
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

Lemma ispo_Dcuts_le_rel : ispo Dcuts_le_rel.
Proof.
  split.
  exact istrans_Dcuts_le_rel.
  exact isrefl_Dcuts_le_rel.
Qed.
Definition Dcuts_le : po Dcuts :=
  popair _ ispo_Dcuts_le_rel.
Definition istrans_Dcuts_le : istrans Dcuts_le :=
  istrans_Dcuts_le_rel.
Definition isrefl_Dcuts_le : isrefl Dcuts_le :=
  isrefl_Dcuts_le_rel.

(** [Dcuts_ge] is a partial order on [Dcuts] *)

Definition Dcuts_ge_rel : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_le Y X.

Lemma istrans_Dcuts_ge_rel : istrans Dcuts_ge_rel.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_le with y.
Qed.
Lemma isrefl_Dcuts_ge_rel : isrefl Dcuts_ge_rel.
Proof.
  now apply isrefl_Dcuts_le.
Qed.

Lemma ispo_Dcuts_ge_rel : ispo Dcuts_ge_rel.
Proof.
  split.
  exact istrans_Dcuts_ge_rel.
  exact isrefl_Dcuts_ge_rel.
Qed.
Definition Dcuts_ge : po Dcuts :=
  popair _ ispo_Dcuts_ge_rel.
Definition istrans_Dcuts_ge : istrans Dcuts_ge :=
  istrans_Dcuts_ge_rel.
Definition isrefl_Dcuts_ge : isrefl Dcuts_ge :=
  isrefl_Dcuts_ge_rel.

(** [Dcuts_eq] is an equality on [Dcuts] *)

Definition Dcuts_eq : hrel Dcuts :=
  fun (X Y : Dcuts) => hconj (Dcuts_le X Y) (Dcuts_ge X Y).

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

Lemma ispo_Dcuts_eq : ispo Dcuts_eq.
Proof.
  split.
  exact istrans_Dcuts_eq.
  exact isrefl_Dcuts_eq.
Qed.

Lemma issymm_Dcuts_eq : issymm Dcuts_eq.
Proof.
  intros x y (Hxy,Hyx).
  now split.
Qed.

Lemma iseqrel_Dcuts_eq : iseqrel Dcuts_eq.
Proof.
  split.
  exact ispo_Dcuts_eq.
  exact issymm_Dcuts_eq.
Qed.

Lemma Dcuts_eq_is_eq :
  forall x y : Dcuts,
    Dcuts_eq x y -> x = y.
Proof.
  intros x y (Hle,Hge).
  apply total2_paths_second_isaprop.
  apply pr2.
  apply funextsec.
  intro r.
  apply weqtopathshProp.
  apply logeqweq ; intros Hr.
  revert Hle ; apply hinhuniv ; intro Hle.
  now apply Hle.
  revert Hge ; apply hinhuniv ; intro Hge.
  now apply Hge.
Qed.

(** *** Strict order and appartness *)

(** [Dcuts_lt] is a strict partial order *)

Definition Dcuts_lt : hrel Dcuts :=
  fun (X Y : Dcuts) =>
    hexists (fun x : NonnegativeRationals => dirprod (neg (x ∈ X)) (x ∈ Y)).
Lemma istrans_Dcuts_lt : istrans Dcuts_lt.
Proof.
  intros x y z.

  apply hinhfun2.
  intros (r,(Xr,Yr)) (n,(Yn,Zn)).
  exists r ; split.
  exact Xr.
  apply is_Dcuts_bot with n.
  exact Zn.
  apply lt_leNonnegativeRationals.
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

Lemma isstpo_Dcuts_lt : isStrictPartialOrder Dcuts_lt.
Proof.
  split.
  exact istrans_Dcuts_lt.
  exact isirrefl_Dcuts_lt.
Qed.

(** [Dcuts_gt] is a strict partial order *)

Definition Dcuts_gt : hrel Dcuts :=
  fun (X Y : Dcuts) => Dcuts_lt Y X.
Lemma istrans_Dcuts_gt : istrans Dcuts_gt.
Proof.
  intros x y z Hxy Hyz.
  now apply istrans_Dcuts_lt with y.
Qed.
Lemma isirrefl_Dcuts_gt : isirrefl Dcuts_gt.
Proof.
  now apply isirrefl_Dcuts_lt.
Qed.

Lemma isstpo_Dcuts_gt : isStrictPartialOrder Dcuts_gt.

Proof.
  split.
  exact istrans_Dcuts_gt.
  exact isirrefl_Dcuts_gt.
Qed.

(** [Dcuts_ap] is an apartness relation *)
(* todo : define apartness relation *)

Definition Dcuts_ap (X Y : Dcuts) : hProp :=
  hdisj (Dcuts_lt X Y) (Dcuts_gt X Y).

Lemma isirrefl_Dcuts_ap : isirrefl Dcuts_ap.
Proof.
  intros x. 
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
  intros [Hap|Hap].
  now apply isirrefl_Dcuts_lt with (1 := Hap).
  now apply isirrefl_Dcuts_lt with (1 := Hap).
Qed.
Lemma issymm_Dcuts_ap : issymm Dcuts_ap.
Proof.
  intros x y.
  apply islogeqcommhdisj.
Qed.

(** *** Various basic theorems about order, equality and apartness *)

Delimit Scope Dcuts_scope with Dcuts.

(** Notations *)

Notation "x <= y" := (Dcuts_le x y) : Dcuts_scope.
Notation "x >= y" := (Dcuts_ge x y) : Dcuts_scope.
Notation "x < y" := (Dcuts_lt x y) : Dcuts_scope.
Notation "x > y" := (Dcuts_gt x y) : Dcuts_scope.

Open Scope Dcuts.

(** Compatibility between order predicates *)

Lemma Dcuts_ge_le :
  forall x y : Dcuts, x >= y -> y <= x.
Proof.
  easy.
Qed.
Lemma Dcuts_le_ge :
  forall x y : Dcuts, x <= y -> y >= x.
Proof.
  easy.
Qed.
Lemma Dcuts_eq_le :
  forall x y : Dcuts, Dcuts_eq x y -> x <= y.
Proof.
  now intros x y (le_xy,ge_xy).
Qed.
Lemma Dcuts_eq_ge :
  forall x y : Dcuts, Dcuts_eq x y -> x >= y.
Proof.
  now intros x y (le_xy,ge_xy).
Qed.
Lemma Dcuts_le_ge_eq :
  forall x y : Dcuts, x <= y -> x >= y -> Dcuts_eq x y.
Proof.
  intros x y le_xy ge_xy.
  now split.
Qed.

Lemma Dcuts_gt_lt :
  forall x y : Dcuts, x > y -> y < x.
Proof.
  easy.
Qed.
Lemma Dcuts_lt_gt :
  forall x y : Dcuts, x < y -> y > x.
Proof.
  easy.
Qed.

Lemma Dcuts_lt_le :
  forall x y : Dcuts, x < y -> x <= y.
Proof.
  intros x y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply lt_leNonnegativeRationals.
  now apply Dcuts_bounded with x.
Qed.
Lemma Dcuts_gt_ge :
  forall x y : Dcuts, x > y -> x >= y.
Proof.
  intros x y.
  now apply Dcuts_lt_le.
Qed.

Lemma Dcuts_le_ngt :
  forall x y : Dcuts, x <= y -> neg (x > y).
Proof.
  unfold neg.
  intros x y ;
    apply (hinhuniv2 (P := hProppair _ isapropempty)) ;
      intros Hxy (r,(Yr,Xr)).
  now apply Yr, Hxy.
Qed.
Lemma Dcuts_gt_nle :
  forall x y : Dcuts, x > y -> neg (x <= y).
Proof.
  intros x y Hlt Hle.
  revert Hlt.
  now apply Dcuts_le_ngt.
Qed.
Lemma Dcuts_ge_nlt :
  forall x y : Dcuts, x >= y -> neg (x < y).
Proof.
  intros X Y.
  now apply Dcuts_le_ngt.
Qed.
Lemma Dcuts_lt_nge :
  forall x y : Dcuts, x < y -> neg (x >= y).
Proof.
  intros x y.
  now apply Dcuts_gt_nle.
Qed.

Lemma Dcuts_eq_nap :
  forall x y : Dcuts, Dcuts_eq x y -> neg (Dcuts_ap x y).
Proof.
  intros X Y [Hxy Hyx].
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
  intros [Hap|Hap].
  now apply Dcuts_ge_nlt in Hyx.
  now apply Dcuts_le_ngt in Hxy.
Qed.

(** Mixed transitivity *)

Lemma istrans_Dcuts_le_lt :
  forall x y z : Dcuts,
    x <= y -> y < z -> x < z.
Proof.
  intros x y z. 
  apply hinhfun2.
  intros Hxy (r,(Yr,Zr)).
  exists r ; split.
  intro Xr ; apply Yr.
  now apply Hxy.
  exact Zr.
Qed.
Lemma istrans_Dcuts_lt_le :
  forall x y z : Dcuts,
    x < y -> y <= z -> x < z.
Proof.
  intros x y z. 
  apply hinhfun2.
  intros (r,(Xr,Yr)) Hyz.
  exists r ; split.
  exact Xr.
  now apply Hyz.
Qed.

(** ** Least Upper Bound *)

Section Dcuts_lub.

Context (E : Dcuts -> hProp).
Context (E_bounded : hexists (isUpperBound Dcuts_le E)).

Definition Dcuts_lub_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun X : Dcuts => dirprod (E X) (r ∈ X)).
Lemma Dcuts_lub_bot : 
  forall (x : NonnegativeRationals),
    Dcuts_lub_val x -> forall y : NonnegativeRationals, (y <= x)%NnR -> Dcuts_lub_val y.
Proof.
  intros r Xr n Xn.
  revert Xr ; apply hinhfun ; intros (X,(Ex,Xr)).
  exists X ; split.
  exact Ex.
  now apply is_Dcuts_bot with r.
Qed.
Lemma Dcuts_lub_open :
  forall (x : NonnegativeRationals),
    Dcuts_lub_val x ->
    hexists (fun y : NonnegativeRationals => dirprod (Dcuts_lub_val y) (x < y)%NnR).
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
   hexists (fun ub : NonnegativeRationals => neg (Dcuts_lub_val ub)).
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

Definition Dcuts_lub (E : Dcuts -> hProp) (E_bounded : hexists (isUpperBound Dcuts_le E)) : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_bounded E E_bounded).

Lemma isub_Dcuts_lub (E : Dcuts -> hProp)
                     (E_bounded : hexists (isUpperBound Dcuts_le E)) :
  isUpperBound Dcuts_le E (Dcuts_lub E E_bounded).
Proof.
  intros ;
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r Hr.
  intros P HP ; apply HP ; clear P HP.
  now exists x.
Qed.
Lemma islbub_Dcuts_lub (E : Dcuts -> hProp) (E_bounded : hexists (isUpperBound Dcuts_le E)) :
  isSmallerThanUpperBounds Dcuts_le E (Dcuts_lub E E_bounded).
Proof.
  intros.
  intros x Hx.  
  intros P HP ; apply HP ; clear P HP.
  intros r ; simpl.
  apply hinhuniv.
  intros (y,(Ey,Yr)).
  apply (Hx y Ey).
  now intros H ; apply H.
Qed.
Lemma islub_Dcuts_lub (E : Dcuts -> hProp) (E_bounded : hexists (isUpperBound Dcuts_le E)) :
  isLeastUpperBound Dcuts_le E (Dcuts_lub E E_bounded).
Proof.
  split.
  exact (isub_Dcuts_lub E E_bounded).
  exact (islbub_Dcuts_lub E E_bounded).
Qed.

(** ** Greatest Lower Bound *)

Section Dcuts_glb.

Context (E : Dcuts -> hProp).
Context (E_not_empty : hexists E).  

Definition Dcuts_glb_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun n => dirprod (r < n)%NnR (forall X : Dcuts, E X -> n ∈ X)).
Lemma Dcuts_glb_bot : 
  forall (x : NonnegativeRationals),
    Dcuts_glb_val x -> forall y : NonnegativeRationals, (y <= x)%NnR -> Dcuts_glb_val y.
Proof.
  intros r Hr n Hn.
  revert Hr ; apply hinhfun ; intros (m,(Hrm,Hr)).
  exists m ; split.
  now apply istrans_le_lt_ltNonnegativeRationals with r.
  easy.
Qed.
Lemma Dcuts_glb_open :
  forall (x : NonnegativeRationals),
    Dcuts_glb_val x ->
    hexists (fun y : NonnegativeRationals => dirprod (Dcuts_glb_val y) (x < y)%NnR).
Proof.
  intros r ; apply hinhfun ; intros (n,(Hrn,Hn)).
  destruct (between_ltNonnegativeRationals _ _ Hrn) as (t,(Hrt,Ttn)).
  exists t.
  split.
  intros P HP ; apply HP ; clear P HP.
  exists n.
  now split.
  exact Hrt.
Qed.
Lemma Dcuts_glb_bounded :
   hexists (fun ub : NonnegativeRationals => neg (Dcuts_glb_val ub)).
Proof.
  revert E_not_empty ; apply hinhuniv ; intros (x,Hx).
  generalize (is_Dcuts_bounded x) ; apply hinhfun ; intros (ub,Hub).
  exists ub.
  unfold neg.
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (n,(Hn,Hn')).
  apply Hub.
  apply is_Dcuts_bot with n.
  now apply Hn'.
  now apply lt_leNonnegativeRationals.
Qed.

End Dcuts_glb.

Definition Dcuts_glb (E : Dcuts -> hProp) (E_not_empty : hexists E) : Dcuts :=
  mk_Dcuts (Dcuts_glb_val E) (Dcuts_glb_bot E) (Dcuts_glb_open E) (Dcuts_glb_bounded E E_not_empty).

Lemma isub_Dcuts_glb (E : Dcuts -> hProp)
                     (E_not_empty : hexists E) :
  isUpperBound Dcuts_ge E (Dcuts_glb E E_not_empty).
Proof.
  intros ;
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r ; apply hinhuniv ; intros (n,(Hrn,Hn)).
  apply is_Dcuts_bot with n.
  now apply Hn.
  now apply lt_leNonnegativeRationals.
Qed.
Lemma islbub_Dcuts_glb (E : Dcuts -> hProp) (E_not_empty : hexists E) :
  isSmallerThanUpperBounds Dcuts_ge E (Dcuts_glb E E_not_empty).
Proof.
  intros ;
  intros x Hx.
  intros P HP ; apply HP ; clear P HP.
  intros r Xr.
  generalize (is_Dcuts_open _ _ Xr)
  ; apply hinhuniv ; intros (n,(Xn,Hrn)).
  intros P HP ; apply HP ; clear P HP.
  exists n.
  split.
  exact Hrn.
  intros y Ey.
  generalize (Hx y Ey).
  apply hinhuniv.
  now intro H ; apply H.
Qed.
Lemma isglb_Dcuts_glb (E : Dcuts -> hProp) (E_not_empty : hexists E) :
  isLeastUpperBound Dcuts_ge E (Dcuts_glb E E_not_empty).
Proof.
  split.
  exact (isub_Dcuts_glb E E_not_empty).
  exact (islbub_Dcuts_glb E E_not_empty).
Qed.

(** ** [Dcuts] is an [abmonoid] *)

Section Dcuts_plus.

  Context (X : subset NonnegativeRationals).
  Context (X_bot : Dcuts_def_bot X).
  Context (X_open : Dcuts_def_open X).
  Context (X_bounded : Dcuts_def_bounded X).
  Context (Y : subset NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_bounded : Dcuts_def_bounded Y).

Definition Dcuts_plus_val : subset NonnegativeRationals :=
  fun r => hdisj (hdisj (X r) (Y r))
                 (hexists (fun xy => dirprod (r = (fst xy + snd xy)%NnR)
                                             (dirprod (X (fst xy)) (Y (snd xy))))).
Lemma Dcuts_plus_bot : Dcuts_def_bot Dcuts_plus_val.
Proof.
  intros r Hr n Hn.
  revert Hr ; apply hinhfun ; intros [Hr | Hr].
  - left.
    revert Hr ; apply hinhfun ; intros [Hr | Hr].
    + left.
      now apply X_bot with r.
    + right.
      now apply Y_bot with r.
  - right.
    revert Hr ; apply hinhfun ; intros [(rx,ry) (Hr,(Hrx,Hry))].
    simpl in Hr, Hrx, Hry.
    (*set (nx := (rx * (n / r))%NnR).
    set (ny := (ry * (n / r))%NnR).
    
Qed.*)
Admitted.

End Dcuts_plus.

(* Definition Dcuts_plus (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_plus_val (pr1 X) (pr1 Y)). *)

(* Lemma isabmonoidop_Dcuts : isabmonoidop Dcuts. *)

(** * Definition of non-negative real numbers *)

Definition NonnegativeReals : hSet := Dcuts.

Definition NonnegativeReals_to_subsetNonnegativeRationals : NonnegativeReals -> (NonnegativeRationals -> hProp) := pr1.
Definition subsetNonnegativeRationals_to_NonnegativeReals
  (X : NonnegativeRationals -> hProp)
  (Xbot : forall x : NonnegativeRationals,
            X x -> forall y : NonnegativeRationals, (y <= x)%NnR -> X y)
  (Xopen : forall x : NonnegativeRationals,
             X x ->
             hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)%NnR))
  (Xtop : hexists (fun ub : NonnegativeRationals => neg (X ub))) : NonnegativeReals :=
  mk_Dcuts X Xbot Xopen Xtop.

(** ** Order *)

Definition leNonnegativeReals : CompleteOrder NonnegativeReals.
Proof.
  exists Dcuts_le.
  intros E Eub Ene.
  exists (Dcuts_lub E Eub).
  apply islub_Dcuts_lub.
Defined.
Definition co_to_po {X : UU} : CompleteOrder X -> po X := pr1.
Coercion co_to_po : CompleteOrder >-> po.

Definition lubNonnegativeReals (E : NonnegativeReals -> hProp) (Eub : hexists (isUpperBound leNonnegativeReals E)) : LeastUpperBound leNonnegativeReals E.
Proof.
  intros.
  exists (Dcuts_lub E Eub).
  apply islub_Dcuts_lub.
Defined.

Definition geNonnegativeReals : CompleteOrder NonnegativeReals.
Proof.
  exists Dcuts_ge.
  intros E Eub Ene.
  exists (Dcuts_glb E Ene).
  apply isglb_Dcuts_glb.
Defined.

Definition glbNonnegativeReals (E : NonnegativeReals -> hProp) (Ene : hexists E) : LeastUpperBound geNonnegativeReals E.
Proof.
  intros.
  exists (Dcuts_glb E Ene).
  apply isglb_Dcuts_glb.
Defined.

Definition ltNonnegativeReals : StrictPartialOrder NonnegativeReals :=
  pairStrictPartialOrder _ isstpo_Dcuts_lt.
Definition gtNonnegativeReals : StrictPartialOrder NonnegativeReals :=
  pairStrictPartialOrder _ isstpo_Dcuts_gt.

(** ** Constants and functions *)

(** ** Theorems *)

(** ** Opacify *)

Global Opaque leNonnegativeReals geNonnegativeReals.
Global Opaque ltNonnegativeReals gtNonnegativeReals.
Global Opaque lubNonnegativeReals.

(* End of the file Dcuts.v *)