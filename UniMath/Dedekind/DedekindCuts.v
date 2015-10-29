(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Sets_comp.
Require Export UniMath.Dedekind.Apartness.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.DivisionRig.
Require Import UniMath.Dedekind.NonnegativeRationals.

Delimit Scope Dcuts_scope with Dcuts.
Open Scope NRat_scope.
Open Scope Dcuts_scope.

(** ** Definition of Dedekind cuts *)

Definition Dcuts_def_bot (X : hsubtypes NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    forall y : NonnegativeRationals, y <= x -> X y.
Definition Dcuts_def_open (X : hsubtypes NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)).
Definition Dcuts_def_finite (X : hsubtypes NonnegativeRationals) : hProp :=
  hexists (fun ub : NonnegativeRationals => neg (X ub)).
Definition Dcuts_def_error (X : hsubtypes NonnegativeRationals) : UU :=
  forall r, 0 < r -> hdisj (neg (X r)) (hexists (λ q, dirprod (X q) (neg (X (q + r))))).

Lemma isaprop_Dcuts_def_bot (X : hsubtypes NonnegativeRationals) : isaprop (Dcuts_def_bot X).
Proof.
  intros X.
  repeat (apply impred_isaprop ; intro).
  now apply pr2.
Qed.
Lemma isaprop_Dcuts_def_open (X : hsubtypes NonnegativeRationals) : isaprop (Dcuts_def_open X).
Proof.
  intros X.
  repeat (apply impred_isaprop ; intro).
  now apply pr2.
Qed.
Lemma isaprop_Dcuts_def_error (X : hsubtypes NonnegativeRationals) : isaprop (Dcuts_def_error X).
Proof.
  intros X.
  repeat (apply impred_isaprop ; intro).
  now apply pr2.
Qed.

Lemma isaprop_Dcuts_hsubtypes (X : hsubtypes NonnegativeRationals) :
  isaprop (Dcuts_def_bot X × Dcuts_def_open X × Dcuts_def_error X).
Proof.
  intro X.
  apply isofhleveldirprod, isofhleveldirprod.
  - exact (isaprop_Dcuts_def_bot X).
  - exact (isaprop_Dcuts_def_open X).
  - exact (isaprop_Dcuts_def_error X).
Qed.

Definition Dcuts_hsubtypes : hsubtypes (hsubtypes NonnegativeRationals) :=
  fun X : hsubtypes NonnegativeRationals => hProppair _ (isaprop_Dcuts_hsubtypes X).
Lemma isaset_Dcuts : isaset (carrier Dcuts_hsubtypes).
Proof.
  apply isasetsubset with pr1.
  apply isasethsubtypes.
  apply isinclpr1.
  intro x.
  apply pr2.
Qed.
Definition Dcuts_set : hSet := hSetpair _ isaset_Dcuts.
Definition pr1Dcuts (x : Dcuts_set) : hsubtypes NonnegativeRationals := pr1 x.
Notation "x ∈ X" := (pr1Dcuts X x) (at level 70, no associativity) : DC_scope.

Open Scope DC_scope.

Lemma is_Dcuts_bot (X : Dcuts_set) : Dcuts_def_bot (pr1 X).
Proof.
  destruct X as [X (Hbot,(Hopen,Hfinite))] ; simpl.
  exact Hbot.
Qed.
Lemma is_Dcuts_open (X : Dcuts_set) : Dcuts_def_open (pr1 X).
Proof.
  destruct X as [X (Hbot,(Hopen,Hfinite))] ; simpl.
  exact Hopen.
Qed.
Lemma is_Dcuts_error (X : Dcuts_set) : Dcuts_def_error (pr1 X).
Proof.
  destruct X as [X (Hbot,(Hopen,Hfinite))] ; simpl.
  now apply Hfinite.
Qed.

Definition mk_Dcuts (X : NonnegativeRationals -> hProp)
                    (Hbot : Dcuts_def_bot X)
                    (Hopen : Dcuts_def_open X)
                    (Herror : Dcuts_def_error X) : Dcuts_set.
Proof.
  intros X Hbot Hopen Herror.
  exists X ; repeat split.
  now apply Hbot.
  now apply Hopen.
  now apply Herror.
Defined.

Lemma Dcuts_finite :
  forall X : Dcuts_set, forall r : NonnegativeRationals,
    neg (r ∈ X) -> forall n : NonnegativeRationals, n ∈ X -> n < r.
Proof.
  intros X r Hr n Hn.
  apply notge_ltNonnegativeRationals ; intro Hn'.
  apply Hr.
  apply is_Dcuts_bot with n.
  exact Hn.
  exact Hn'.
Qed.

(** ** Equivalence on [Dcuts] *)

Definition Dcuts_eq_rel :=
  λ X Y : Dcuts_set, ∀ r : NonnegativeRationals, (r ∈ X -> r ∈ Y) × (r ∈ Y -> r ∈ X).
Lemma isaprop_Dcuts_eq_rel : forall X Y : Dcuts_set, isaprop (Dcuts_eq_rel X Y).
Proof.
  intros X Y.
  apply impred_isaprop ; intro r.
  apply isapropdirprod.
  - now apply isapropimpl, pr2.
  - now apply isapropimpl, pr2.
Qed.
Definition Dcuts_eq : hrel Dcuts_set :=
  λ X Y : Dcuts_set, hProppair (forall r, dirprod (r ∈ X -> r ∈ Y) (r ∈ Y -> r ∈ X)) (isaprop_Dcuts_eq_rel X Y).

Lemma istrans_Dcuts_eq : istrans Dcuts_eq.
Proof.
  intros x y z Hxy Hyz r.
  split.
  - intros Xr.
    now apply (pr1 (Hyz r)), (pr1 (Hxy r)), Xr.
  - intros Zr.
    now apply (pr2 (Hxy r)), (pr2 (Hyz r)), Zr.
Qed.
Lemma isrefl_Dcuts_eq : isrefl Dcuts_eq.
Proof.
  intros x r.
  now split.
Qed.
Lemma ispo_Dcuts_eq : ispo Dcuts_eq.
Proof.
  split.
  exact istrans_Dcuts_eq.
  exact isrefl_Dcuts_eq.
Qed.

Lemma issymm_Dcuts_eq : issymm Dcuts_eq.
Proof.
  intros x y Hxy r.
  split.
  exact (pr2 (Hxy r)).
  exact (pr1 (Hxy r)).
Qed.

Lemma iseqrel_Dcuts_eq : iseqrel Dcuts_eq.
Proof.
  split.
  exact ispo_Dcuts_eq.
  exact issymm_Dcuts_eq.
Qed.

Lemma Dcuts_eq_is_eq :
  forall x y : Dcuts_set,
    Dcuts_eq x y -> x = y.
Proof.
  intros x y Heq.
  apply total2_paths_second_isaprop.
  - apply pr2.
  - apply funextsec.
    intro r.
    apply uahp.
    exact (pr1 (Heq r)).
    exact (pr2 (Heq r)).
Qed.

(** ** Pre-orders and apartness on [Dcuts] *)

(** Strict partial order on [Dcuts] *)

Definition Dcuts_lt_rel : hrel Dcuts_set :=
  fun (X Y : Dcuts_set) =>
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
  now apply Dcuts_finite with y.
Qed.
Lemma isirrefl_Dcuts_lt_rel : isirrefl Dcuts_lt_rel.
Proof.
  intros x.
  unfold neg ;
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (r,(nXr,Xr)).
  now apply nXr.
Qed.
Lemma iscotrans_Dcuts_lt_rel :
  iscotrans Dcuts_lt_rel.
Proof.
  intros x y z.
  apply hinhuniv ; intros (r,(Xr,Zr)).
  generalize (is_Dcuts_open z r Zr) ; apply hinhuniv ; intros (r',(Zr',Hr)).
  assert (Hr0 : 0%NRat < r' - r) by (now rewrite minusNonnegativeRationals_gt0).
  generalize (is_Dcuts_error y _ Hr0) ; apply hinhuniv ; intros [Yq | Yq].
  - apply Utilities.squash_element ;
    right ; apply Utilities.squash_element.
    exists r' ; split.
    + intro H0 ; apply Yq.
      apply is_Dcuts_bot with r'.
      exact H0.
      now apply NQminusle.
    + exact Zr'.
  - revert Yq ; apply hinhfun ; intros (q,(Yq,nYq)).
    destruct (isdecrel_leNonnegativeRationals (q + (r' - r)) r') as [Hdec | Hdec].
    + right ; apply hinhpr.
      exists r' ; split.
      intro Yr' ; apply nYq.
      apply is_Dcuts_bot with r'.
      exact Yr'.
      exact Hdec.
      exact Zr'.
    + left ; apply hinhpr.
      exists q ; split.
      * intro Xq ; apply Xr.
        apply is_Dcuts_bot with q.
        exact Xq.
        apply notge_ltNonnegativeRationals in Hdec.
        rewrite <- (plusNonnegativeRationals_ltcompat_r r), isassoc_plusNonnegativeRationals, minusNonegativeRationals_plusr, iscomm_plusNonnegativeRationals, plusNonnegativeRationals_ltcompat_r in Hdec.
        now apply lt_leNonnegativeRationals, Hdec.
        now apply lt_leNonnegativeRationals, Hr.
      * exact Yq.
Qed.

Lemma isstpo_Dcuts_lt_rel : isStrongOrder Dcuts_lt_rel.
Proof.
  split.
  exact istrans_Dcuts_lt_rel.
  exact isirrefl_Dcuts_lt_rel.
Qed.

Local Notation "x < y" := (Dcuts_lt_rel x y) : Dcuts_scope.

(** ** Apartness on [Dcuts] *)

Definition Dcuts_ap_rel (X Y : Dcuts_set) : hProp :=
  (X < Y) ∨ (Y < X).

Lemma isirrefl_Dcuts_ap_rel : isirrefl Dcuts_ap_rel.
Proof.
  intros x.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
  intros [Hap|Hap].
  now apply isirrefl_Dcuts_lt_rel with (1 := Hap).
  now apply isirrefl_Dcuts_lt_rel with (1 := Hap).
Qed.
Lemma issymm_Dcuts_ap_rel : issymm Dcuts_ap_rel.
Proof.
  intros x y.
  apply islogeqcommhdisj.
Qed.
Lemma iscotrans_Dcuts_ap_rel : iscotrans Dcuts_ap_rel.
Proof.
  intros x y z.
  apply hinhuniv ; intros [Hap|Hap].
  - generalize (iscotrans_Dcuts_lt_rel _ y _ Hap) ; apply hinhfun.
    intros [Hy | Hy].
    + now left ; apply hinhpr ; left.
    + now right ; apply hinhpr ; left.
  - generalize (iscotrans_Dcuts_lt_rel _ y _ Hap) ; apply hinhfun.
    intros [Hy | Hy].
    + now right ; apply hinhpr ; right.
    + now left ; apply hinhpr ; right.
Qed.

Definition Dcuts : apSet :=
  Dcuts_set,, Dcuts_ap_rel,,
       isirrefl_Dcuts_ap_rel,, issymm_Dcuts_ap_rel,, iscotrans_Dcuts_ap_rel.

(** * Algebraic structures on Dcuts *)

(** ** From non negative rational numbers to Dedekind cuts *)

Lemma NonnegativeRationals_to_Dcuts_bot (q : NonnegativeRationals) :
  Dcuts_def_bot (λ r : NonnegativeRationals, (r < q)%NRat).
Proof.
  intros q r Hr n Hnr.
  now apply istrans_le_lt_ltNonnegativeRationals with r.
Qed.
Lemma NonnegativeRationals_to_Dcuts_open (q : NonnegativeRationals) :
  Dcuts_def_open (λ r : NonnegativeRationals, (r < q)%NRat).
Proof.
  intros q r Hr.
  apply hinhpr.
  destruct (between_ltNonnegativeRationals r q Hr) as [n (Hrn,Hnq)].
  exists n.
  now split.
Qed.
Lemma NonnegativeRationals_to_Dcuts_error (q : NonnegativeRationals) :
  Dcuts_def_error (λ r : NonnegativeRationals, (r < q)%NRat).
Proof.
  intros q.
  intros r Hr0.
  intros P HP ; apply HP ; clear P HP.
  destruct (isdecrel_ltNonnegativeRationals r q) as [Hqr|Hqr].
  - right.
    assert (Hn0 : (0 < q - r)%NRat) by (now rewrite minusNonnegativeRationals_gt0).
    intros P HP ; apply HP ; clear P HP.
    exists (q - r).
    split.
    + rewrite <- (plusNonnegativeRationals_ltcompat_r r).
      rewrite minusNonegativeRationals_plusr.
      pattern q at 1 ;
        rewrite <- isrunit_zeroNonnegativeRationals.
      rewrite plusNonnegativeRationals_ltcompat_l.
      exact Hr0.
      now apply lt_leNonnegativeRationals, Hqr.
    + rewrite minusNonegativeRationals_plusr.
      now apply isirrefl_StrongOrder.
      now apply lt_leNonnegativeRationals, Hqr.
  - now left.
Qed.

Definition NonnegativeRationals_to_Dcuts (q : NonnegativeRationals) : Dcuts :=
  mk_Dcuts (fun r => (r < q)%NRat)
           (NonnegativeRationals_to_Dcuts_bot q)
           (NonnegativeRationals_to_Dcuts_open q)
           (NonnegativeRationals_to_Dcuts_error q).

Definition Dcuts_zero : Dcuts := NonnegativeRationals_to_Dcuts 0%NRat.
Definition Dcuts_one : Dcuts := NonnegativeRationals_to_Dcuts 1%NRat.

Notation "0" := Dcuts_zero : Dcuts_scope.
Notation "1" := Dcuts_one : Dcuts_scope.

Lemma Dcuts_zero_empty :
  forall r : NonnegativeRationals, r ∈ 0 = hProppair empty isapropempty.
Proof.
  intros r ; simpl.
  apply uahp ; simpl.
  - now apply isnonnegative_NonnegativeRationals'.
  - easy.
Qed.
Lemma Dcuts_notempty :
  forall x : Dcuts, 0%NRat ∈ x = hexists (λ r, r ∈ x × (0 < r)%NRat).
Proof.
  intros x ; simpl.
  apply weqtopathshProp, logeqweq ; simpl.
  - intro H.
    now apply is_Dcuts_open.
  - apply hinhuniv ; intros (r,(Xr,Hr0)).
    apply is_Dcuts_bot with r.
    + exact Xr.
    + now apply lt_leNonnegativeRationals.
Qed.
Lemma Dcuts_notempty_notzero :
  forall x, 0%NRat ∈ x -> x != 0.
Proof.
  intros x Hx Hx0.
  rewrite Hx0 in Hx.
  now rewrite (Dcuts_zero_empty 0%NRat) in Hx.
Qed.


(** ** [Dcuts] is an [abmonoid] *)

Section Dcuts_plus.

  Context (X : hsubtypes NonnegativeRationals).
  Context (X_bot : Dcuts_def_bot X).
  Context (X_open : Dcuts_def_open X).
  Context (X_error : Dcuts_def_error X).
  Context (Y : hsubtypes NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_error : Dcuts_def_error Y).

Definition Dcuts_plus_val : hsubtypes NonnegativeRationals :=
  fun r => hdisj (hdisj (X r) (Y r))
                 (hexists (fun xy => dirprod (r = (fst xy + snd xy)%NRat)
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
    revert Hr ; apply hinhfun ; intros [(rx,ry) (Hr,(Hrx,Hry))] ; simpl in Hr,Hrx,Hry.
    destruct (isdeceq_NonnegativeRationals r 0%NRat) as [Hr0 | Hr0].
    + rewrite Hr0 in Hn.
      rewrite <- NonnegativeRationals_eq0_le0 in Hn.
      exists (0%NRat,0%NRat).
      rewrite Hn ; simpl.
      repeat split.
      * now rewrite isrunit_zeroNonnegativeRationals.
      * apply X_bot with (1 := Hrx).
        apply isnonnegative_NonnegativeRationals.
      * apply Y_bot with (1 := Hry).
        apply isnonnegative_NonnegativeRationals.
    + set (nx := (rx * (n / r))%NRat).
      set (ny := (ry * (n / r))%NRat).
      exists (nx,ny).
      repeat split.
      * unfold nx,ny ; simpl.
        rewrite <- isrdistr_mult_plusNonnegativeRationals, <- Hr.
        rewrite multdivNonnegativeRationals.
        reflexivity.
        intro ; now apply Hr0.
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
Lemma Dcuts_plus_error : Dcuts_def_error Dcuts_plus_val.
Proof.
  intros c Hc.
  rewrite NQhalf_is_pos in Hc.
  generalize (X_error _ Hc) (Y_error _ Hc).
  apply hinhfun2 ; intros [Hx [Hy | Hy ] | Hx [Hy | Hy] ].
  - left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
    + apply hinhuniv ; intros [Hz | Hz].
      * apply Hx.
        apply X_bot with (1 := Hz).
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply NonnegativeRationals_leplus_r.
      * apply Hy.
        apply Y_bot with (1 := Hz).
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply NonnegativeRationals_leplus_r.
    + apply hinhuniv ; intros ((rx,ry),(Hz,(Xr,Yr))).
      simpl in Hz,Xr,Yr.
      destruct (isdecrel_ltNonnegativeRationals rx (c / 2)) as [Hx' | Hx'].
      destruct (isdecrel_ltNonnegativeRationals ry (c / 2)) as [Hy' | Hy'].
      * apply (isirrefl_StrongOrder ltNonnegativeRationals c).
        pattern c at 1 ; rewrite Hz.
        rewrite (NQhalf_double c).
        apply NonnegativeRationals_plusltcompat.
        exact Hx'.
        exact Hy'.
      * apply Hy.
        apply Y_bot with (1 := Yr).
        now apply notlt_geNonnegativeRationals, Hy'.
      * apply Hx.
        apply X_bot with (1 := Xr).
        now apply notlt_geNonnegativeRationals, Hx'.
  - right.
    revert Hy ; apply hinhfun ; intros (q,(Yq,nYq)).
    exists q ; split.
    apply hinhpr.
    left.
    apply hinhpr.
    right ; exact Yq.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
    apply hinhuniv ; intros [Xq | Yq'].
    + apply Hx ; apply X_bot with (1 := Xq).
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply NonnegativeRationals_leplus_l.
    + apply nYq ; apply Y_bot with (1 := Yq').
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply NonnegativeRationals_leplus_r.
    + apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
      simpl in Hr,Xr,Yr.
      apply (isirrefl_StrongOrder ltNonnegativeRationals (q + c)).
      pattern (q + c) at 1 ; rewrite Hr.
      rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      rewrite iscomm_plusNonnegativeRationals.
      apply NonnegativeRationals_plusltcompat.
      apply notge_ltNonnegativeRationals ; intro H.
      apply nYq ; apply Y_bot with (1 := Yr).
      exact H.
      apply notge_ltNonnegativeRationals ; intro H.
      apply Hx ; apply X_bot with (1 := Xr).
      exact H.
  - right.
    revert Hx ; apply hinhfun ; intros (q,(Xq,nXq)).
    exists q ; split.
    apply hinhpr.
    left.
    apply hinhpr.
    left ; exact Xq.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
    apply hinhuniv ; intros [Xq' | Yq].
    + apply nXq ; apply X_bot with (1 := Xq').
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply NonnegativeRationals_leplus_r.
    + apply Hy ; apply Y_bot with (1 := Yq).
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply NonnegativeRationals_leplus_l.
    + apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
      simpl in Hr,Xr,Yr.
      apply (isirrefl_StrongOrder ltNonnegativeRationals (q + c)).
      pattern (q + c) at 1 ; rewrite Hr.
      rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply NonnegativeRationals_plusltcompat.
      apply notge_ltNonnegativeRationals ; intro H.
      apply nXq ; apply X_bot with (1 := Xr).
      exact H.
      apply notge_ltNonnegativeRationals ; intro H.
      apply Hy ; apply Y_bot with (1 := Yr).
      exact H.
  - right.
    revert Hx Hy ; apply hinhfun2 ;
    intros (qx,(Xq,nXq)) (qy,(Yq,nYq)).
    exists (qx + qy).
    split.
    + apply hinhpr.
      right.
      apply hinhpr.
      exists (qx,qy) ; repeat split.
      * exact Xq.
      * exact Yq.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
      apply hinhuniv ; intros [Xq' | Yq'].
      * apply nXq, X_bot with (1 := Xq').
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)).
        rewrite (iscomm_plusNonnegativeRationals qy).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals (qx + (c/2))).
        apply NonnegativeRationals_leplus_r.
      * apply nYq, Y_bot with (1 := Yq').
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)).
        rewrite (iscomm_plusNonnegativeRationals _ (qy + _)).
        rewrite (isassoc_plusNonnegativeRationals (qy + (c/2))).
        apply NonnegativeRationals_leplus_r.
      * apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
        simpl in Hr, Xr, Yr.
        apply (isirrefl_StrongOrder ltNonnegativeRationals (qx + qy + c)).
        pattern (qx + qy + c) at 1 ; rewrite Hr.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)).
        rewrite (iscomm_plusNonnegativeRationals qy).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals (qx + (c/2))).
        apply NonnegativeRationals_plusltcompat.
        apply notge_ltNonnegativeRationals ; intro H.
        apply nXq ; apply X_bot with (1 := Xr) ; exact H.
        apply notge_ltNonnegativeRationals ; intro H.
        apply nYq ; apply Y_bot with (1 := Yr) ; exact H.
Qed.

End Dcuts_plus.

Definition Dcuts_plus (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_plus_val (pr1 X) (pr1 Y))
           (Dcuts_plus_bot (pr1 X) (is_Dcuts_bot X)
                           (pr1 Y) (is_Dcuts_bot Y))
           (Dcuts_plus_open (pr1 X) (is_Dcuts_open X)
                            (pr1 Y) (is_Dcuts_open Y))
           (Dcuts_plus_error (pr1 X) (is_Dcuts_bot X) (is_Dcuts_error X)
                              (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_error Y)).

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
  apply Dcuts_eq_is_eq ; intro r ; split.
  - now apply H.
  - now apply H.
Qed.
Lemma isassoc_Dcuts_plus : isassoc Dcuts_plus.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq ; intro r ; split.
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
  apply Dcuts_eq_is_eq ; intro r ; split.
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

(** Effectively Ordered Set *)

Lemma Dcuts_lt_le_rel :
  forall x y : Dcuts, Dcuts_lt_rel x y -> Dcuts_le_rel x y.
Proof.
  intros x y ; apply hinhfun ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply lt_leNonnegativeRationals.
  now apply Dcuts_finite with x.
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

Notation "x <= y" := (Dcuts_le x y) : Dcuts_scope.
Notation "x >= y" := (Dcuts_ge x y) : Dcuts_scope.
Notation "x < y" := (Dcuts_lt x y) : Dcuts_scope.
Notation "x > y" := (Dcuts_gt x y) : Dcuts_scope.

Lemma Dcuts_eq_notap :
  forall x y : Dcuts, x = y -> neg (x # y).
Proof.
  intros x y ->.
  now apply isirrefl_Dcuts_ap_rel.
Qed.

Lemma Dcuts_apzero_notempty :
  forall x, (x # 0) = (0%NRat ∈ x).
Proof.
  intros x.
  rewrite Dcuts_notempty.
  apply weqtopathshProp, logeqweq ; apply hinhuniv.
  - intros [Hr|Hr] ; revert Hr.
    + apply hinhfun ; intros (r,(Xr,Or)).
      now rewrite Dcuts_zero_empty in Or.
    + apply hinhuniv ; intros (r,(_,Xr)).
      generalize (is_Dcuts_open _ _ Xr).
      apply hinhfun ; intros (q,(Xq,Hq)).
      exists q ; split.
      exact Xq.
      apply istrans_le_lt_ltNonnegativeRationals with r.
      now apply isnonnegative_NonnegativeRationals.
      exact Hq.
  - intros (r,(Xr,Hr0)).
    intros P HP ; apply HP ; clear P HP.
    right.
    intros P HP ; apply HP ; clear P HP.
    exists r ; split.
    now rewrite Dcuts_zero_empty.
    exact Xr.
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
  intros x y Heq.
  apply hinhpr.
  intro r ;
    now apply (pr1 (Heq _)).
Qed.
Lemma Dcuts_eq_ge :
  forall x y : Dcuts, Dcuts_eq x y -> x >= y.
Proof.
  intros x y Heq.
  apply Dcuts_eq_le.
  now apply issymm_Dcuts_eq.
Qed.
Lemma Dcuts_le_ge_eq :
  forall x y : Dcuts, x <= y -> x >= y -> Dcuts_eq x y.
Proof.
  intros x y ; apply hinhuniv2 ; intros le_xy ge_xy r.
  split.
  now apply le_xy.
  now apply ge_xy.
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
  forall x y : Dcuts, Dcuts_eq x y -> neg (x # y).
Proof.
  intros X Y Heq.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
  intros [Hap|Hap].
  - now apply Dcuts_eq_ge, Dcuts_ge_nlt in Heq.
  - now apply Dcuts_eq_le, (Dcuts_le_ngt_rel X Y) in Heq.
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

(** ** Least Upper Finite *)

Section Dcuts_lub.

Context (E : hsubtypes Dcuts).
Context (E_bounded : hexists (@isUpperBound eo_Dcuts E)).
Context (E_cauchy: forall c, (0 < c)%NRat -> hdisj (@isUpperBound eo_Dcuts E (NonnegativeRationals_to_Dcuts c)) (hexists (λ P, E P × @isUpperBound eo_Dcuts E (Dcuts_plus P (NonnegativeRationals_to_Dcuts c))))).

Definition Dcuts_lub_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun X : Dcuts => dirprod (E X) (r ∈ X)).
Lemma Dcuts_lub_bot :
  forall (x : NonnegativeRationals),
    Dcuts_lub_val x -> forall y : NonnegativeRationals, (y <= x)%NRat -> Dcuts_lub_val y.
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
    hexists (fun y : NonnegativeRationals => dirprod (Dcuts_lub_val y) (x < y)%NRat).
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
(*Lemma Dcuts_lub_finite :
   hexists (fun ub : NonnegativeRationals => neg (Dcuts_lub_val ub)).
Proof.
  revert E_bounded.
  apply hinhuniv.
  intros (M,HM).
  generalize (is_Dcuts_finite M).
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
Qed.*)
Lemma Dcuts_lub_error:
  Dcuts_def_error Dcuts_lub_val.
Proof.
  intros c Hc.
  rewrite NQhalf_is_pos in Hc.
  generalize (E_cauchy _ Hc).
  apply hinhuniv ; intros [He | ].
  intros P HP ; apply HP ; clear P HP.
  - left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (X,(EX,Xc)).
    generalize (He _ EX).
    apply hinhuniv.
    intros H.
    generalize (H _ Xc) ; simpl.
    apply EOle_not_EOlt.
    pattern c at 2.
    rewrite (NQhalf_double c).
    apply NonnegativeRationals_leplus_r.
  - apply hinhuniv ; intros (X,(EX,Hx)).
    generalize (is_Dcuts_error X _ Hc).
    apply hinhfun ; intros [Xc | ].
    + left.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (Y,(EY,Yc)).
      generalize (Hx _ EY).
      apply hinhuniv.
      intros H.
      generalize (H _ Yc).
      apply hinhuniv ; intros [ | ].
      apply hinhuniv ; intros [ Xc' | Yc' ].
      * apply Xc.
        apply is_Dcuts_bot with (1 := Xc').
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply NonnegativeRationals_leplus_r.
      * revert Yc' ; simpl.
        apply EOle_not_EOlt.
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply NonnegativeRationals_leplus_r.
      * apply hinhuniv.
        intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply Xc, is_Dcuts_bot with (1 := Xc').
        apply NonnegativeRationals_pluslecancel_r with cy.
        rewrite <- Hc'.
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply NonnegativeRationals_pluslecompat_l.
        now apply lt_leNonnegativeRationals.
    + intro ; right.
      revert h ; apply hinhfun ; intros (q,(Xq,nXq)).
      exists q ; split.
      intros P HP ; apply HP ; clear P HP.
      now exists X ; split.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (Y,(EY,Yc)).
      generalize (Hx _ EY).
      apply hinhuniv.
      intros H.
      generalize (H _ Yc).
      apply hinhuniv ; intros [ | ].
      apply hinhuniv ; intros [ Xc' | Yc' ].
      * apply nXq.
        apply is_Dcuts_bot with (1 := Xc').
        pattern c at 2.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply NonnegativeRationals_leplus_r.
      * revert Yc' ; simpl.
        apply EOle_not_EOlt.
        pattern c at 2.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply NonnegativeRationals_leplus_l.
      * apply hinhuniv.
        intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply nXq, is_Dcuts_bot with (1 := Xc').
        apply NonnegativeRationals_pluslecancel_r with cy.
        rewrite <- Hc'.
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply NonnegativeRationals_pluslecompat_l.
        now apply lt_leNonnegativeRationals.
Qed.

End Dcuts_lub.

Definition Dcuts_lub (E : hsubtypes eo_Dcuts) E_cauchy : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_error E E_cauchy).

Lemma isub_Dcuts_lub (E : hsubtypes eo_Dcuts) E_cauchy :
  isUpperBound E (Dcuts_lub E E_cauchy).
Proof.
  intros ;
  intros x Ex.
  intros P HP ; apply HP ; clear P HP.
  intros r Hr.
  intros P HP ; apply HP ; clear P HP.
  now exists x.
Qed.
Lemma islbub_Dcuts_lub (E : hsubtypes eo_Dcuts) E_cauchy :
  isSmallerThanUpperBounds E (Dcuts_lub E E_cauchy).
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
Lemma islub_Dcuts_lub (E : hsubtypes eo_Dcuts) E_cauchy :
  isLeastUpperBound E (Dcuts_lub E E_cauchy).
Proof.
  split.
  exact (isub_Dcuts_lub E E_cauchy).
  exact (islbub_Dcuts_lub E E_cauchy).
Qed.

(*(** ** Greatest Lower Bound *)

Section Dcuts_glb.

Context (E : hsubtypes Dcuts).
Context (E_not_empty : hexists E).

Definition Dcuts_glb_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun n => dirprod (r < n)%NRat (forall X : Dcuts, E X -> n ∈ X)).
Lemma Dcuts_glb_bot :
  forall (x : NonnegativeRationals),
    Dcuts_glb_val x -> forall y : NonnegativeRationals, (y <= x)%NRat -> Dcuts_glb_val y.
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
    hexists (fun y : NonnegativeRationals => dirprod (Dcuts_glb_val y) (x < y)%NRat).
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
(*Lemma Dcuts_glb_finite :
   hexists (fun ub : NonnegativeRationals => neg (Dcuts_glb_val ub)).
Proof.
  revert E_not_empty ; apply hinhuniv ; intros (x,Hx).
  generalize (is_Dcuts_finite x) ; apply hinhfun ; intros (ub,Hub).
  exists ub.
  unfold neg.
  apply (hinhuniv (P := hProppair _ isapropempty)).
  intros (n,(Hn,Hn')).
  apply Hub.
  apply is_Dcuts_bot with n.
  now apply Hn'.
  now apply lt_leNonnegativeRationals.
Qed.*)
Lemma Dcuts_glb_error :
  Dcuts_def_error Dcuts_glb_val.
Proof.
  intros c Hc.
  revert E_not_empty ; apply hinhuniv ; intros (X,EX).
  generalize (is_Dcuts_error X _ Hc).
  apply hinhfun ; intros [Xc | Xc].
  - left ; unfold neg.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (n,(Hn,Hn')).
    apply Xc, is_Dcuts_bot with (1 := Hn' _ EX).
    now apply lt_leNonnegativeRationals.
  - right.

Qed.

End Dcuts_glb.

Definition Dcuts_glb (E : hsubtypes eo_Dcuts) (E_not_empty : hexists E) : Dcuts :=
  mk_Dcuts (Dcuts_glb_val E) (Dcuts_glb_bot E) (Dcuts_glb_open E). (Dcuts_glb_error E E_not_empty).

Lemma isub_Dcuts_glb (E : hsubtypes eo_Dcuts)
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
Lemma islbub_Dcuts_glb (E : hsubtypes eo_Dcuts) (E_not_empty : hexists E) :
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
Lemma isglb_Dcuts_glb (E : hsubtypes eo_Dcuts) (E_not_empty : hexists E) :
  isGreatestLowerBound E (Dcuts_glb E E_not_empty).
Proof.
  split.
  exact (isub_Dcuts_glb E E_not_empty).
  exact (islbub_Dcuts_glb E E_not_empty).
Qed.*)

(** * Definition of non-negative real numbers *)

Definition NonnegativeReals : hSet := Dcuts.

Definition NonnegativeReals_to_hsubtypesNonnegativeRationals : NonnegativeReals -> (hsubtypes NonnegativeRationals) := pr1.
Definition hsubtypesNonnegativeRationals_to_NonnegativeReals
  (X : NonnegativeRationals -> hProp)
  (Xbot : forall x : NonnegativeRationals,
            X x -> forall y : NonnegativeRationals, (y <= x)%NRat -> X y)
  (Xopen : forall x : NonnegativeRationals,
             X x ->
             hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)%NRat))
  (Xtop : Dcuts_def_error X) : NonnegativeReals :=
  mk_Dcuts X Xbot Xopen Xtop.

(** ** Order *)

Definition leNonnegativeReals : po NonnegativeReals := Dcuts_le.
Definition geNonnegativeReals : po NonnegativeReals := Dcuts_ge.
Definition ltNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_lt.
Definition gtNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_gt.

Definition lubNonnegativeReals (E : hsubtypes NonnegativeReals) Eub :
  LeastUpperBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_lub E Eub) (islub_Dcuts_lub E Eub).

(*Definition glbNonnegativeReals (E : hsubtypes NonnegativeReals) (Ene : hexists E) : GreatestLowerBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_glb E Ene) (isglb_Dcuts_glb E Ene).*)

(** ** Constants and functions *)

(** ** Theorems *)

(** ** Opacify *)

Global Opaque leNonnegativeReals geNonnegativeReals.
Global Opaque ltNonnegativeReals gtNonnegativeReals.
Global Opaque lubNonnegativeReals (*glbNonnegativeReals*).

(* End of the file Dcuts.v *)