(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.NonnegativeRationals.

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

(** ** [Dcuts] is a effectively ordered set *)

(** Partial order on [Dcuts] *)

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

(** Strict partial order on [Dcuts] *)

Definition Dcuts_lt_rel : hrel Dcuts :=
  fun (X Y : Dcuts) =>
    hexists (fun x : NonnegativeRationals => dirprod (neg (x ∈ X)) (x ∈ Y)).

Lemma istrans_Dcuts_lt_rel : istrans Dcuts_lt_rel.
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
Lemma isirrefl_Dcuts_lt_rel : isirrefl Dcuts_lt_rel.
Proof.
  intros x.
  unfold neg ;
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (r,(nXr,Xr)).
  now apply nXr.
Qed.

Lemma isstpo_Dcuts_lt_rel : isStrongOrder Dcuts_lt_rel.
Proof.
  split.
  exact istrans_Dcuts_lt_rel.
  exact isirrefl_Dcuts_lt_rel.
Qed.

(** Effectively Ordered Set *)

Lemma Dcuts_lt_le_rel :
  forall x y : Dcuts, Dcuts_lt_rel x y -> Dcuts_le_rel x y.
Proof.
  intros x y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply lt_leNonnegativeRationals.
  now apply Dcuts_bounded with x.
Qed.

Lemma Dcuts_le_ngt_rel :
  forall x y : Dcuts, Dcuts_le_rel x y -> Dcuts_lt_rel y x -> empty.
Proof.
  intros x y ;
    apply (hinhuniv2 (P := hProppair _ isapropempty)) ;
      intros Hxy (r,(Yr,Xr)).
  now apply Yr, Hxy.
Qed.

Lemma iseo_Dcuts_le_lt_rel :
  isEffectiveOrder Dcuts_le_rel Dcuts_lt_rel.
Proof.
  split.
  - split.
    + exact ispo_Dcuts_le_rel.
    + exact isstpo_Dcuts_lt_rel.
  - split.
    + exact Dcuts_lt_le_rel.
    + exact Dcuts_le_ngt_rel.
Qed.

Definition iseo_Dcuts : EffectiveOrder Dcuts :=
  pairEffectiveOrder Dcuts_le_rel Dcuts_lt_rel iseo_Dcuts_le_lt_rel.

Definition eo_Dcuts : EffectivelyOrderedSet :=
  pairEffectivelyOrderedSet iseo_Dcuts.

Definition Dcuts_le : po Dcuts := @EOle eo_Dcuts.
Definition Dcuts_ge : po Dcuts := @EOge eo_Dcuts.
Definition Dcuts_lt : StrongOrder Dcuts := @EOlt eo_Dcuts.
Definition Dcuts_gt : StrongOrder Dcuts := @EOgt eo_Dcuts.

Delimit Scope Dcuts_scope with Dcuts.

Open Scope Dcuts_scope.

Notation "x <= y" := (Dcuts_le x y) : Dcuts_scope.
Notation "x >= y" := (Dcuts_ge x y) : Dcuts_scope.
Notation "x < y" := (Dcuts_lt x y) : Dcuts_scope.
Notation "x > y" := (Dcuts_gt x y) : Dcuts_scope.
     
(** ** Equality on [Dcuts] *)

Definition Dcuts_eq : hrel Dcuts :=
  fun (X Y : Dcuts) => hconj (X <= Y) (Y <= X).

Lemma istrans_Dcuts_eq : istrans Dcuts_eq.
Proof.
  intros x y z (Hxy,Hyx) (Hyz,Hzy).
  split.
  now apply istrans_po with y.
  now apply istrans_po with y.
Qed.
Lemma isrefl_Dcuts_eq : isrefl Dcuts_eq.
Proof.
  intros x.
  split.
  now apply isrefl_po.
  now apply isrefl_po.
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

(** ** Apartness on [Dcuts] *)
(* todo : define apartness relation *)

Definition Dcuts_ap (X Y : Dcuts) : hProp :=
  hdisj (Dcuts_lt X Y) (Dcuts_gt X Y).

Lemma isirrefl_Dcuts_ap : isirrefl Dcuts_ap.
Proof.
  intros x. 
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
  intros [Hap|Hap].
  now apply isirrefl_StrongOrder with (1 := Hap).
  now apply isirrefl_StrongOrder with (1 := Hap).
Qed.
Lemma issymm_Dcuts_ap : issymm Dcuts_ap.
Proof.
  intros x y.
  apply islogeqcommhdisj.
Qed.

(** *** Various basic theorems about order, equality and apartness *)


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


Lemma Dcuts_gt_ge :
  forall x y : Dcuts, x > y -> x >= y.
Proof.
  intros x y.
  now apply Dcuts_lt_le_rel.
Qed.

Lemma Dcuts_gt_nle :
  forall x y : Dcuts, x > y -> neg (x <= y).
Proof.
  intros x y Hlt Hle.
  revert Hlt.
  now apply Dcuts_le_ngt_rel.
Qed.
Lemma Dcuts_ge_nlt :
  forall x y : Dcuts, x >= y -> neg (x < y).
Proof.
  intros X Y Hxy Hyx.
  now apply (Dcuts_le_ngt_rel Y X).
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
  now apply (Dcuts_le_ngt_rel X Y) in Hxy.
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

Context (E : subset Dcuts).
Context (E_bounded : hexists (@isUpperBound eo_Dcuts E)).

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

Definition Dcuts_lub (E : subset eo_Dcuts) (E_bounded : hexists (isUpperBound E)) : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_bounded E E_bounded).

Lemma isub_Dcuts_lub (E : subset eo_Dcuts)
                     (E_bounded : hexists (isUpperBound E)) :
  isUpperBound E (Dcuts_lub E E_bounded).
Proof.
  intros ;
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r Hr.
  intros P HP ; apply HP ; clear P HP.
  now exists x.
Qed.
Lemma islbub_Dcuts_lub (E : subset eo_Dcuts) (E_bounded : hexists (isUpperBound E)) :
  isSmallerThanUpperBounds E (Dcuts_lub E E_bounded).
Proof.
  intros.
  intros x Hx ; simpl.
  apply hinhpr.
  intros r ; apply hinhuniv ;
  intros (y,(Ey,Yr)).
  generalize (Hx y Ey).
  apply hinhuniv.
  now intros H ; apply H.
Qed.
Lemma islub_Dcuts_lub (E : subset eo_Dcuts) (E_bounded : hexists (isUpperBound E)) :
  isLeastUpperBound E (Dcuts_lub E E_bounded).
Proof.
  split.
  exact (isub_Dcuts_lub E E_bounded).
  exact (islbub_Dcuts_lub E E_bounded).
Qed.

(** ** Greatest Lower Bound *)

Section Dcuts_glb.

Context (E : subset Dcuts).
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

Definition Dcuts_glb (E : subset eo_Dcuts) (E_not_empty : hexists E) : Dcuts :=
  mk_Dcuts (Dcuts_glb_val E) (Dcuts_glb_bot E) (Dcuts_glb_open E) (Dcuts_glb_bounded E E_not_empty).

Lemma isub_Dcuts_glb (E : subset eo_Dcuts)
                     (E_not_empty : hexists E) :
  isLowerBound E (Dcuts_glb E E_not_empty).
Proof.
  intros ;
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r ; apply hinhuniv ; intros (n,(Hrn,Hn)).
  apply is_Dcuts_bot with n.
  now apply Hn.
  now apply lt_leNonnegativeRationals.
Qed.
Lemma islbub_Dcuts_glb (E : subset eo_Dcuts) (E_not_empty : hexists E) :
  isBiggerThanLowerBounds E (Dcuts_glb E E_not_empty).
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
Lemma isglb_Dcuts_glb (E : subset eo_Dcuts) (E_not_empty : hexists E) :
  isGreatestLowerBound E (Dcuts_glb E E_not_empty).
Proof.
  split.
  exact (isub_Dcuts_glb E E_not_empty).
  exact (islbub_Dcuts_glb E E_not_empty).
Qed.

(** * Algebraic structures on Dcuts *)

(** ** From non negative rational numbers to Dedekind cuts *)

Lemma NonnegativeRationals_to_Dcuts_bot (q : NonnegativeRationals) :
  Dcuts_def_bot (λ r : NonnegativeRationals, (r < q)%NnR).
Proof.
  intros q r Hr n Hnr.
  now apply istrans_le_lt_ltNonnegativeRationals with r.
Qed.
Lemma NonnegativeRationals_to_Dcuts_open (q : NonnegativeRationals) :
  Dcuts_def_open (λ r : NonnegativeRationals, (r < q)%NnR).
Proof.
  intros q r Hr.
  apply hinhpr.
  destruct (between_ltNonnegativeRationals r q Hr) as [n (Hrn,Hnq)].
  exists n.
  now split.
Qed.
Lemma NonnegativeRationals_to_Dcuts_bounded (q : NonnegativeRationals) :
  Dcuts_def_bounded (λ r : NonnegativeRationals, (r < q)%NnR).
Proof.
  intros q.
  apply hinhpr.
  exists q.
  now apply isirrefl_StrongOrder.
Qed.

Definition NonnegativeRationals_to_Dcuts (q : NonnegativeRationals) : Dcuts :=
  mk_Dcuts (fun r => (r < q)%NnR)
           (NonnegativeRationals_to_Dcuts_bot q)
           (NonnegativeRationals_to_Dcuts_open q)
           (NonnegativeRationals_to_Dcuts_bounded q).

Definition Dcuts_zero : Dcuts := NonnegativeRationals_to_Dcuts 0%NnR.
Definition Dcuts_one : Dcuts := NonnegativeRationals_to_Dcuts 1%NnR.

Notation "0" := Dcuts_zero : Dcuts_scope.
Notation "1" := Dcuts_one : Dcuts_scope.

Lemma Dcuts_zero_empty :
  forall r : NonnegativeRationals, r ∈ 0 = hProppair empty isapropempty.
Proof.
  intros r ; simpl.
  apply weqtopathshProp, logeqweq ; simpl.
  - now apply isnonnegative_NonnegativeRationals'.
  - easy.
Qed.

(** ** [Dcuts] is an [abmonoid] *)

Lemma NonnegativeRationals_leplus_r :
  forall r q : NonnegativeRationals, (r <= r + q)%NnR.
Admitted.
Lemma NonnegativeRationals_leplus_l :
  forall r q : NonnegativeRationals, (r <= q + r)%NnR.
Admitted.
Lemma isdecrel_leNonnegativeRationals : isdecrel leNonnegativeRationals.
Admitted.
Lemma NonnegativeRationals_pluslecancel_r :
  forall r q n : NonnegativeRationals, (q + r <= n + r)%NnR -> (q <= n)%NnR.
Admitted.
                                          
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
    revert Hr ; apply hinhfun ; intros [(rx,ry) (Hr,(Hrx,Hry))] ; simpl in * |-.
    destruct (isdeceq_NonnegativeRationals r 0%NnR) as [Hr0 | Hr0].
    + rewrite Hr0 in Hn.
      apply NonnegativeRationals_le0_eq0 in Hn.
      exists (0%NnR,0%NnR).
      rewrite Hn ; simpl.
      repeat split.
      * now rewrite NonnegativeRationals_plus0r.
      * apply X_bot with (1 := Hrx).
        apply isnonnegative_NonnegativeRationals.
      * apply Y_bot with (1 := Hry).
        apply isnonnegative_NonnegativeRationals.
    + set (nx := (rx * (n / r))%NnR).
      set (ny := (ry * (n / r))%NnR).
      exists (nx,ny).
      repeat split.
      * unfold nx,ny ; simpl.
        rewrite <- isrdistr_mult_plusNonnegativeRationals, <- Hr.
        now rewrite multdivNonnegativeRationals.
      * apply X_bot with (1 := Hrx).
        apply multrle1NonnegativeRationals.
        now apply ledivle1NonnegativeRationals.
      * apply Y_bot with (1 := Hry).
        apply multrle1NonnegativeRationals.
        now apply ledivle1NonnegativeRationals.
Qed.

Lemma Dcuts_plus_open : Dcuts_def_open Dcuts_plus_val.
Proof.
  intros r.
  apply hinhuniv, sumofmaps.
  - apply hinhuniv, sumofmaps ; intro Hr.
    + generalize (X_open r Hr).
      apply hinhfun ; intros (n,(Xn,Hrn)).
      exists n.
      split.
      * apply hinhpr ; left.
        now apply hinhpr ; left.
      * exact Hrn.
    + generalize (Y_open r Hr).
      apply hinhfun ; intros (n,(Yn,Hrn)).
      exists n.
      split.
      * apply hinhpr ; left.
        now apply hinhpr ; right.
      * exact Hrn.
  - apply hinhuniv ; intros ((rx,ry),(Hr,(Hx,Hy))) ; simpl in * |-.
    generalize (X_open rx Hx) (Y_open ry Hy).
    apply hinhfun2.
    intros (nx,(Xn,Hnx)) (ny,(Yn,Hny)).
    exists (nx + ny).
    split.
    + apply hinhpr ; right.
      apply hinhpr ; exists (nx , ny).
      repeat split.
      * exact Xn.
      * exact Yn.
    + rewrite Hr.
      now apply NonnegativeRationals_plusltcompat.
Qed.
Lemma Dcuts_plus_bounded : Dcuts_def_bounded Dcuts_plus_val.
Proof.
  revert X_bounded Y_bounded.
  apply hinhfun2.
  intros (r,Xr) (n,Yn).
  exists (r + n).
  unfold neg.
  apply (hinhuniv (P := hProppair _ isapropempty)), sumofmaps.
  - apply hinhuniv, sumofmaps.
    + intro Hx ; apply Xr.
      apply X_bot with (1 := Hx).
      now apply NonnegativeRationals_leplus_r.
    + intro Hy ; apply Yn.
      apply Y_bot with (1 := Hy).
      now apply NonnegativeRationals_leplus_l.
  - apply hinhuniv ; intros ((rx,ry),(Hr,(Hx,Hy))) ; simpl in * |-.
    destruct (isdecrel_leNonnegativeRationals r rx).
    apply Xr.
    now apply X_bot with (1 := Hx).
    apply Yn.
    apply Y_bot with (1 := Hy).
    apply istrans_leNonnegativeRationals with ((rx + ry) - r)%NnR.
    rewrite <- Hr.
    admit.
    apply NonnegativeRationals_pluslecancel_r with r.
    admit.
Admitted.

End Dcuts_plus.

Definition Dcuts_plus (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_plus_val (pr1 X) (pr1 Y))
           (Dcuts_plus_bot (pr1 X) (is_Dcuts_bot X)
                           (pr1 Y) (is_Dcuts_bot Y))
           (Dcuts_plus_open (pr1 X) (is_Dcuts_open X)
                            (pr1 Y) (is_Dcuts_open Y))
           (Dcuts_plus_bounded (pr1 X) (is_Dcuts_bot X) (is_Dcuts_open X) (is_Dcuts_bounded X)
                               (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_open Y) (is_Dcuts_bounded Y)).

Lemma iscomm_Dcuts_plus : iscomm Dcuts_plus.
Proof.
  assert (H : forall x y, ∀ x0 : NonnegativeRationals, x0 ∈ Dcuts_plus x y -> x0 ∈ Dcuts_plus y x).
  { intros x y r.
    apply hinhuniv, sumofmaps ; apply hinhuniv ; simpl pr1.
    - apply sumofmaps ; intros Hr.
      + apply hinhpr ; left.
        now apply hinhpr ; right.
      + apply hinhpr ; left.
        now apply hinhpr ; left.
    - intros ((rx,ry),(Hr,(Hx,Hy))) ; simpl in * |-.
      apply hinhpr ; right.
      apply hinhpr ; exists (ry,rx).
      repeat split.
      + rewrite Hr.
        apply iscomm_plusNonnegativeRationals.
      + exact Hy.
      + exact Hx.
  }
  intros x y.
  apply Dcuts_eq_is_eq ; split ; apply hinhpr.
  - exact (H x y).
  - exact (H y x).
Qed.
Lemma isassoc_Dcuts_plus : isassoc Dcuts_plus.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq ; split ; apply hinhpr ; intro r.
  - apply hinhuniv, sumofmaps ; apply hinhuniv ; simpl pr1.
    + apply sumofmaps.
      * apply hinhuniv, sumofmaps ; apply hinhuniv.
        { apply sumofmaps ; intros Hr.
          - apply hinhpr ; left.
            now apply hinhpr ; left.
          - apply hinhpr ; left.
            apply hinhpr ; right.
            apply hinhpr ; left.
            now apply hinhpr ; left. }
        { intros ((rx,ry),(Hr,(Hx,Hy))) ; simpl in * |-.
          apply hinhpr ; right.
          apply hinhpr ; exists (rx,ry).
          repeat split.
          - exact Hr.
          - exact Hx.
          - apply hinhpr ; left.
            now apply hinhpr ; left. }
      * intros Hr.
        apply hinhpr ; left.
        apply hinhpr ; right.
        apply hinhpr ; left.
        now apply hinhpr ; right.
    + intros ((xy,rz),(Hr,(Hxy,Hz))) ; simpl in * |- .
      revert Hxy ; apply hinhuniv, sumofmaps ; apply hinhuniv.
      * apply sumofmaps ; intros Hxy.
        { apply hinhpr ; right.
          apply hinhpr ; exists (xy,rz).
          repeat split.
          - exact Hr.
          - exact Hxy.
          - apply hinhpr ; left.
            now apply hinhpr ; right. }
        { apply hinhpr ; left.
          apply hinhpr ; right.
          apply hinhpr ; right.
          apply hinhpr ; exists (xy,rz).
          repeat split.
          - exact Hr.
          - exact Hxy.
          - exact Hz. }
      * intros ((rx,ry),(Hxy,(Hx,Hy))) ; simpl in * |-.
        apply hinhpr ; right.
        apply hinhpr ; exists (rx,ry + rz).
        repeat split ; simpl.
        { rewrite Hr, Hxy.
          now apply isassoc_plusNonnegativeRationals. }
        { exact Hx. }
        { apply hinhpr ; right.
          apply hinhpr ; exists (ry,rz).
          repeat split.
          - exact Hy.
          - exact Hz. }
  - apply hinhuniv, sumofmaps ; apply hinhuniv ; simpl pr1.
    + apply sumofmaps.
      * intros Hr.
        apply hinhpr ; left.
        apply hinhpr ; left.
        apply hinhpr ; left.
        now apply hinhpr ; left.
      * apply hinhuniv, sumofmaps ; apply hinhuniv.
        { apply sumofmaps ; intros Hr.
          - apply hinhpr ; left.
            apply hinhpr ; left.
            apply hinhpr ; left.
            now apply hinhpr ; right.
          - apply hinhpr ; left.
            now apply hinhpr ; right. }
        { intros ((ry,rz),(Hr,(Hy,Hz))) ; simpl in * |-.
          apply hinhpr ; right.
          apply hinhpr ; exists (ry,rz).
          repeat split.
          - exact Hr.
          - apply hinhpr ; left.
            now apply hinhpr ; right.
          - exact Hz. }
    + intros ((rx,yz),(Hr,(Hx,Hyz))) ; simpl in * |- .
      revert Hyz ; apply hinhuniv, sumofmaps ; apply hinhuniv.
      * apply sumofmaps ; intros Hyz.
        { apply hinhpr ; left.
          apply hinhpr ; left.
          apply hinhpr ; right.
          apply hinhpr ; exists (rx,yz).
          repeat split.
          - exact Hr.
          - exact Hx.
          - exact Hyz. }
        { apply hinhpr ; right.
          apply hinhpr ; exists (rx,yz).
          repeat split.
          - exact Hr.
          - apply hinhpr ; left.
            now apply hinhpr ; left.
          - exact Hyz. }
      * intros ((ry,rz),(Hyz,(Hy,Hz))) ; simpl in * |-.
        apply hinhpr ; right.
        apply hinhpr ; exists ((rx+ry), rz).
        repeat split ; simpl.
        { rewrite Hr, Hyz.
          now rewrite isassoc_plusNonnegativeRationals. }
        { apply hinhpr ; right.
          apply hinhpr ; exists (rx,ry).
          repeat split.
          - exact Hx.
          - exact Hy. }
        { exact Hz. }
Qed.
Lemma islunit_Dcuts_plus_zero : islunit Dcuts_plus 0.
Proof.
  intros x.
  apply Dcuts_eq_is_eq ; split ; apply hinhpr ; intro r.
  - apply hinhuniv, sumofmaps ; apply hinhuniv.
    + apply sumofmaps ; intro Hr.
      * now rewrite Dcuts_zero_empty in Hr.
      * exact Hr.
    + intros ((r0,rx),(_,(Hr,_))).
      now rewrite Dcuts_zero_empty in Hr.
  - intros Hr.
    apply hinhpr ; left.
    now apply hinhpr ; right.
Qed.
Lemma isrunit_Dcuts_plus_zero : isrunit Dcuts_plus 0.
Proof.
  intros x.
  rewrite iscomm_Dcuts_plus.
  now apply islunit_Dcuts_plus_zero.
Qed.
Definition ismonoidop_Dcuts_plus : ismonoidop Dcuts_plus.
Proof.
  split.
  - apply isassoc_Dcuts_plus.
  - exists Dcuts_zero.
    split.
    + exact islunit_Dcuts_plus_zero.
    + exact isrunit_Dcuts_plus_zero.
Defined.

Definition isabmonoidop_Dcuts : isabmonoidop Dcuts_plus.
Proof.
  split.
  - exact ismonoidop_Dcuts_plus.
  - exact iscomm_Dcuts_plus.
Defined.

Definition Dcuts_with_plus : setwithbinop :=
  setwithbinoppair Dcuts Dcuts_plus.

Definition Dcuts_addmonoid : abmonoid := 
  abmonoidpair Dcuts_with_plus isabmonoidop_Dcuts.

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

Definition leNonnegativeReals : po NonnegativeReals := Dcuts_le.
Definition geNonnegativeReals : po NonnegativeReals := Dcuts_ge.
Definition ltNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_lt.
Definition gtNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_gt.

Definition lubNonnegativeReals (E : subset NonnegativeReals) (Eub : hexists (isUpperBound (X := eo_Dcuts) E)) :
  LeastUpperBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_lub E Eub) (islub_Dcuts_lub E Eub).

Definition glbNonnegativeReals (E : subset NonnegativeReals) (Ene : hexists E) : GreatestLowerBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_glb E Ene) (isglb_Dcuts_glb E Ene).

(** ** Constants and functions *)

(** ** Theorems *)

(** ** Opacify *)

Global Opaque leNonnegativeReals geNonnegativeReals.
Global Opaque ltNonnegativeReals gtNonnegativeReals.
Global Opaque lubNonnegativeReals glbNonnegativeReals.

(* End of the file Dcuts.v *)