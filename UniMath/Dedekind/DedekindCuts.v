(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Sets_comp.
Require Export UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.NonnegativeRationals.

Delimit Scope Dcuts_scope with Dcuts.
Local Open Scope NRat_scope.
Local Open Scope Dcuts_scope.
Local Open Scope constructive_logic.

(** ** Definition of Dedekind cuts *)

Definition Dcuts_def_bot (X : hsubtypes NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    forall y : NonnegativeRationals, y <= x -> X y.
Definition Dcuts_def_open (X : hsubtypes NonnegativeRationals) : UU :=
  forall x : NonnegativeRationals, X x ->
    hexists (fun y : NonnegativeRationals => (X y) × (x < y)).
Definition Dcuts_def_finite (X : hsubtypes NonnegativeRationals) : hProp :=
  hexists (fun ub : NonnegativeRationals => ¬ (X ub)).
Definition Dcuts_def_error (X : hsubtypes NonnegativeRationals) : UU :=
  forall r, 0 < r -> (¬ (X r)) ∨ (hexists (λ q, (X q) × (¬ (X (q + r))))).
Definition Dcuts_def_error' (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) : UU :=
  forall r, 0 < r -> r <= k -> (¬ (X r)) ∨ (hexists (λ q, (0 < q) × (X q) × (¬ (X (q + r))))).

Lemma Dcuts_def_error'_correct1 (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) :
  Dcuts_def_bot X -> Dcuts_def_open X ->
  Dcuts_def_error X -> Dcuts_def_error' X k.
Proof.
  intros X k Hbot Hopen H r Hr0 _.
  generalize (H r Hr0) ; clear H.
  apply hinhfun ; intros [H | H].
  - now left.
  - right.
    revert H ; apply hinhuniv ; intros (q,(Xq,nXq)).
    generalize (Hopen q Xq) ; clear Hopen ; apply hinhfun ; intros (q0,(Xq0,Hq0)).
    exists q0 ; repeat split.
    + apply istrans_le_lt_ltNonnegativeRationals with (2 := Hq0).
      now apply isnonnegative_NonnegativeRationals.
    + exact Xq0.
    + intro H ; apply nXq.
      apply Hbot with (1 := H).
      now apply NonnegativeRationals_pluslecompat_r, lt_leNonnegativeRationals.
Qed.
Lemma Dcuts_def_error'_correct2 (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) :
  Dcuts_def_bot X -> (0 < k)%NRat ->
  Dcuts_def_error' X k -> Dcuts_def_error X.
Proof.
  intros X k Hbot Hk0 H r Hr0.
  destruct (isdecrel_leNonnegativeRationals r k) as [Hrk | Hrk].
  - generalize (H r Hr0 Hrk) ; clear H ; apply hinhfun ; intros [H | H].
    + now left.
    + right.
      revert H ; apply hinhfun ; intros (q,(_,Hq)).
      exists q ; exact Hq.
  - apply notge_ltNonnegativeRationals in Hrk.
    generalize (H _ Hk0 (isrefl_leNonnegativeRationals k)) ; clear H ; apply hinhfun ; intros [H | H].
    + left.
      intros H0 ; apply H.
      apply Hbot with (1 := H0).
      now apply lt_leNonnegativeRationals.
    + right.
      revert H ; apply hinhfun ; intros (q,(_,(Xq,nXq))).
      exists q ; split.
      * exact Xq.
      * intro H ; apply nXq.
        apply Hbot with (1 := H).
        now apply NonnegativeRationals_pluslecompat_l, lt_leNonnegativeRationals.
Qed.

Lemma Dcuts_def_error_finite (X : hsubtypes NonnegativeRationals) :
  Dcuts_def_error X -> Dcuts_def_finite X.
Proof.
  intros X Hx.
  specialize (Hx _ ispositive_oneNonnegativeRationals).
  revert Hx ; apply hinhuniv ; intros [Hx|Hx].
  - apply hinhpr.
    exists 1 ; exact Hx.
  - revert Hx ; apply hinhfun ; intros (x,(_,Hx)).
    exists (x + 1) ; exact Hx.
Qed.

Lemma Dcuts_def_error_not_empty (X : hsubtypes NonnegativeRationals) :
  X 0 -> Dcuts_def_error X ->
  forall c : NonnegativeRationals,
    (0 < c)%NRat -> hexists (λ x : NonnegativeRationals, X x × ¬ X (x + c)).
Proof.
  intros X X0 Hx c Hc.
  generalize (Hx c Hc).
  apply hinhuniv ; intros [ nXc | Hx' ].
  - apply hinhpr ; exists 0%NRat ; split.
    exact X0.
    rewrite islunit_zeroNonnegativeRationals.
    exact nXc.
  - exact Hx'.
Qed.

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
Lemma ispreorder_Dcuts_eq : ispreorder Dcuts_eq.
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
  exact ispreorder_Dcuts_eq.
  exact issymm_Dcuts_eq.
Qed.

Lemma Dcuts_eq_is_eq :
  forall x y : Dcuts_set,
    Dcuts_eq x y -> x = y.
Proof.
  intros x y Heq.
  apply subtypeEquality.
  - now intro ; apply pr2.
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
      now apply NonnegativeRationals_leminus.
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

Lemma Dcuts_eq_notap :
  forall x y : Dcuts, x = y -> neg (x # y).
Proof.
  intros x y ->.
  now apply isirrefl_Dcuts_ap_rel.
Qed.

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


Local Lemma isapfun_NonnegativeRationals_to_Dcuts_aux :
  forall q q' : NonnegativeRationals,
    NonnegativeRationals_to_Dcuts q < NonnegativeRationals_to_Dcuts q'
    = (q < q')%NRat.
Proof.
  intros q q'.
  apply uahp.
  - apply hinhuniv.
    intros (r,(Qr,Q'r)).
    apply istrans_le_lt_ltNonnegativeRationals with r.
    + apply notlt_geNonnegativeRationals.
      exact Qr.
    + exact Q'r.
  - intros H.
    apply hinhpr.
    exists q ; split.
    now apply (isirrefl_ltNonnegativeRationals q).
    exact H.
Qed.
Lemma isapfun_NonnegativeRationals_to_Dcuts :
  forall q q' : NonnegativeRationals,
    NonnegativeRationals_to_Dcuts q # NonnegativeRationals_to_Dcuts q'
    -> q != q'.
Proof.
  intros q q'.
  apply (hinhuniv (P := hProppair _ (isapropneg _))).
  intros [Hap | Hap].
  now apply ltNonnegativeRationals_noteq ; rewrite <- isapfun_NonnegativeRationals_to_Dcuts_aux.
  now apply gtNonnegativeRationals_noteq ; rewrite lt_gtNonnegativeRationals, <- isapfun_NonnegativeRationals_to_Dcuts_aux.
Qed.
Lemma isapfun_NonnegativeRationals_to_Dcuts' :
  forall q q' : NonnegativeRationals,
    q != q'
    -> NonnegativeRationals_to_Dcuts q # NonnegativeRationals_to_Dcuts q'.
Proof.
  intros q q' H.
  apply hinhpr.
  rewrite ! isapfun_NonnegativeRationals_to_Dcuts_aux.
  rewrite <- (lt_gtNonnegativeRationals q).
  now apply noteq_ltorgtNonnegativeRationals.
Qed.

Definition Dcuts_zero : Dcuts := NonnegativeRationals_to_Dcuts 0%NRat.
Definition Dcuts_one : Dcuts := NonnegativeRationals_to_Dcuts 1%NRat.

Notation "0" := Dcuts_zero : Dcuts_scope.
Notation "1" := Dcuts_one : Dcuts_scope.

(** Various usefull theorems *)

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
  intros x.
  apply uahp.
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

(** ** Addition in Dcuts *)

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
        now rewrite <- NonnegativeRationals_neq0_gt0.
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
      destruct (isdecrel_ltNonnegativeRationals rx (c / 2)%NRat) as [Hx' | Hx'].
      destruct (isdecrel_ltNonnegativeRationals ry (c / 2)%NRat) as [Hy' | Hy'].
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
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)%NRat).
        rewrite (iscomm_plusNonnegativeRationals qy).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals (qx + (c/2)%NRat)).
        apply NonnegativeRationals_leplus_r.
      * apply nYq, Y_bot with (1 := Yq').
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)%NRat).
        rewrite (iscomm_plusNonnegativeRationals _ (qy + _)).
        rewrite (isassoc_plusNonnegativeRationals (qy + (c/2)%NRat)).
        apply NonnegativeRationals_leplus_r.
      * apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
        simpl in Hr, Xr, Yr.
        apply (isirrefl_StrongOrder ltNonnegativeRationals (qx + qy + c)).
        pattern (qx + qy + c) at 1 ; rewrite Hr.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)%NRat).
        rewrite (iscomm_plusNonnegativeRationals qy).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals (qx + (c/2)%NRat)).
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

(** ** Multiplication in Dcuts *)

Section Dcuts_NQmult.

  Context (x : NonnegativeRationals).
  Context (Hx : (0 < x)%NRat).
  Context (Y : hsubtypes NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_finite : Dcuts_def_finite Y).
  Context (Y_error : Dcuts_def_error Y).

Definition Dcuts_NQmult_val : hsubtypes NonnegativeRationals :=
  fun r => hexists (λ ry : NonnegativeRationals, r = x * ry × Y ry).

Lemma Dcuts_NQmult_bot : Dcuts_def_bot Dcuts_NQmult_val.
Proof.
  intros r Hr n Hn.
  revert Hr ; apply hinhfun ;
  intros (ry,(Hr,Hry)) ; simpl in Hr, Hry.
  destruct (isdeceq_NonnegativeRationals r 0%NRat) as [Hr0 | Hr0].
  - rewrite Hr0 in Hn.
    rewrite <- NonnegativeRationals_eq0_le0 in Hn.
    exists 0%NRat.
    rewrite Hn ; simpl.
    split.
    + now rewrite israbsorb_zero_multNonnegativeRationals.
    + apply Y_bot with (1 := Hry).
      apply isnonnegative_NonnegativeRationals.
  - set (ny := (ry * (n / r))%NRat).
    exists ny.
    split.
    + unfold ny ; simpl.
      rewrite <- isassoc_multNonnegativeRationals, <- Hr.
      rewrite multdivNonnegativeRationals.
      reflexivity.
      now rewrite <- NonnegativeRationals_neq0_gt0.
    + apply Y_bot with (1 := Hry).
      apply multrle1NonnegativeRationals.
      now apply ledivle1NonnegativeRationals.
Qed.
Lemma Dcuts_NQmult_open : Dcuts_def_open Dcuts_NQmult_val.
Proof.
  intros r.
  apply hinhuniv ; intros (ry,(Hr,Hry)) ; simpl in Hr, Hry.
  generalize (Y_open ry Hry).
  apply hinhfun.
  intros (ny,(Yn,Hny)).

  exists (x * ny).
  split.
  - apply hinhpr ; exists ny.
    split.
    + reflexivity.
    + exact Yn.
  - rewrite Hr.
    now rewrite multNonnegativeRationals_lt_l.
Qed.
Lemma Dcuts_NQmult_finite : Dcuts_def_finite Dcuts_NQmult_val.
Proof.
  revert Y_finite.
  apply hinhfun.
  intros (y,Hy).
  exists (x * y).
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
  intros (ry,(Hz,Yr)) ; simpl in Hz,Yr.
  revert Hz.
  apply gtNonnegativeRationals_noteq.
  generalize (multNonnegativeRationals_lt_l x ry y Hx).
  simpl.
  unfold hrel_reverse ; simpl.
  intros ->.
  apply (notge_ltNonnegativeRationals ry y).
  intro Hy' ; apply Hy.
  now apply Y_bot with ry.
Qed.

Lemma Dcuts_NQmult_error : Dcuts_def_error Dcuts_NQmult_val.
Proof.
  intros c Hc.
  assert (Hcx : (0 < c / x)%NRat) by (now apply ispositive_divNonnegativeRationals).
  generalize (Y_error _ Hcx).
  apply hinhfun ; intros [Hy | Hy].
  - left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
    intros (ry,(Hz,Yr)) ; simpl in Hz,Yr.
    revert Hz.
    apply gtNonnegativeRationals_noteq.
    rewrite <- (multdivNonnegativeRationals c x).
    generalize (multNonnegativeRationals_lt_l x ry (c / x)%NRat Hx).
    simpl.
    unfold hrel_reverse ; simpl.
    intros ->.
    apply (notge_ltNonnegativeRationals ry (c / x)%NRat).
    intro Hy' ; apply Hy.
    now apply Y_bot with ry.
    exact Hx.
  - right.
    revert Hy ; apply hinhfun ; intros (q,(Yq,nYq)).
    exists (x * q).
    split.
    + apply hinhpr.
      exists q.
      now split.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
      intros (ry,(Hz,Yr)) ; simpl in Hz,Yr.
      revert Hz.
      apply gtNonnegativeRationals_noteq.
      rewrite <- (multdivNonnegativeRationals c x), <-isldistr_mult_plusNonnegativeRationals.
      generalize (multNonnegativeRationals_lt_l x ry (q + c / x)%NRat Hx).
      simpl.
      unfold hrel_reverse ; simpl.
      intros ->.
      apply (notge_ltNonnegativeRationals ry (q + c / x)%NRat).
      intro Hy' ; apply nYq.
      now apply Y_bot with ry.
      exact Hx.
Qed.

End Dcuts_NQmult.

Lemma Dcuts_NQmult_id :
  ∀ X x y, x * y = 1%NRat -> Dcuts_NQmult_val x (Dcuts_NQmult_val y X) = X.
Proof.
  intros X x y H1.
  apply funextfun.
  intros q.
  apply uahp.
  - apply hinhuniv ; intros (r,(->)).
    apply hinhuniv ; intros (s,(->)).
    now rewrite <- isassoc_multNonnegativeRationals, H1, islunit_oneNonnegativeRationals.
  - intros Xq.
    apply hinhpr ; exists (y * q) ; split.
    now rewrite <- isassoc_multNonnegativeRationals, H1, islunit_oneNonnegativeRationals.
    now apply hinhpr ; exists q ; split.
Qed.

Definition Dcuts_NQmult x (Y : Dcuts) Hx : Dcuts :=
  mk_Dcuts (Dcuts_NQmult_val x (pr1 Y))
           (Dcuts_NQmult_bot x (pr1 Y) (is_Dcuts_bot Y))
           (Dcuts_NQmult_open x Hx (pr1 Y) (is_Dcuts_open Y))
           (Dcuts_NQmult_error x Hx (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_error Y)).

Section Dcuts_mult.

  Context (X : hsubtypes NonnegativeRationals).
  Context (X_bot : Dcuts_def_bot X).
  Context (X_open : Dcuts_def_open X).
  Context (X_finite : Dcuts_def_finite X).
  Context (X_error : Dcuts_def_error X).
  Context (Y : hsubtypes NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_finite : Dcuts_def_finite Y).
  Context (Y_error : Dcuts_def_error Y).

Definition Dcuts_mult_val : hsubtypes NonnegativeRationals :=
  fun r => hexists (λ xy : NonnegativeRationals * NonnegativeRationals,
                           r = (fst xy * snd xy)%NRat × X (fst xy) × Y (snd xy)).

Lemma Dcuts_mult_bot : Dcuts_def_bot Dcuts_mult_val.
Proof.
  intros r Hr n Hn.
  revert Hr ; apply hinhfun ;
  intros ((rx,ry),(Hr,(Hrx,Hry))) ; simpl in Hr, Hrx, Hr.
  destruct (isdeceq_NonnegativeRationals r 0%NRat) as [Hr0 | Hr0].
  - rewrite Hr0 in Hn.
    rewrite <- NonnegativeRationals_eq0_le0 in Hn.
    exists (0%NRat,0%NRat).
    rewrite Hn ; simpl.
    repeat split.
    + now rewrite israbsorb_zero_multNonnegativeRationals.
    + apply X_bot with (1 := Hrx).
      apply isnonnegative_NonnegativeRationals.
    + apply Y_bot with (1 := Hry).
      apply isnonnegative_NonnegativeRationals.
  - set (nx := rx).
    set (ny := (ry * (n / r))%NRat).
    exists (nx,ny).
    repeat split.
    + unfold nx,ny ; simpl.
      rewrite <- isassoc_multNonnegativeRationals, <- Hr.
      rewrite multdivNonnegativeRationals.
      reflexivity.
      now rewrite <- NonnegativeRationals_neq0_gt0.
    + exact Hrx.
    + apply Y_bot with (1 := Hry).
      apply multrle1NonnegativeRationals.
      now apply ledivle1NonnegativeRationals.
Qed.
Lemma Dcuts_mult_open : Dcuts_def_open Dcuts_mult_val.
Proof.
  intros r.
  apply hinhuniv ; intros ((rx,ry),(Hr,(Hx,Hy))) ; simpl in Hr, Hx,Hy.
  generalize (X_open rx Hx) (Y_open ry Hy).
  apply hinhfun2.
  intros (nx,(Xn,Hnx)) (ny,(Yn,Hny)).
  exists (nx * ny).
  split.
  - apply hinhpr ; exists (nx , ny).
    repeat split.
    + exact Xn.
    + exact Yn.
  - rewrite Hr.
    now apply multNonnegativeRationals_lt.
Qed.
Lemma Dcuts_mult_finite : Dcuts_def_finite Dcuts_mult_val.
Proof.
  revert X_finite Y_finite.
  apply hinhfun2.
  intros (x,Hx) (y,Hy).
  exists (x * y).
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
  intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
  destruct (isdecrel_ltNonnegativeRationals rx x) as [Hx' | Hx'].
  destruct (isdecrel_ltNonnegativeRationals ry y) as [Hy' | Hy'].
  - apply (isirrefl_StrongOrder ltNonnegativeRationals (x * y)).
    pattern (x * y) at 1 ; rewrite Hz.
    now apply multNonnegativeRationals_lt.
  - apply Hy.
    apply Y_bot with (1 := Yr).
    now apply notlt_geNonnegativeRationals, Hy'.
  - apply Hx.
    apply X_bot with (1 := Xr).
    now apply notlt_geNonnegativeRationals, Hx'.
Qed.

Context (Hx1 : ¬ X 1%NRat).

Lemma Dcuts_mult_error_aux : Dcuts_def_error Dcuts_mult_val.
Proof.
  intros c Hc0.
  rewrite NQhalf_is_pos in Hc0.
  generalize (Y_error _ Hc0).
  apply hinhuniv ; intros [Hy | Hy].
  - apply hinhpr ; left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
    intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
    revert Hz.
    apply gtNonnegativeRationals_noteq.
    rewrite <- (islunit_oneNonnegativeRationals c).
    apply multNonnegativeRationals_lt.
    apply notge_ltNonnegativeRationals ; intro H.
    now apply Hx1, X_bot with (1 := Xr).
    apply notge_ltNonnegativeRationals ; intro H.
    apply Hy, Y_bot with (1 := Yr).
    apply istrans_leNonnegativeRationals with (2 := H).
    pattern c at 2 ; rewrite (NQhalf_double c).
    now apply NonnegativeRationals_leplus_r.
  - revert Hy ; apply hinhuniv ; intros (y,(Yy,nYy)).
    assert (Hq1 : (0 < y + c / 2)%NRat).
    { apply istrans_lt_le_ltNonnegativeRationals with (c / 2)%NRat.
      exact Hc0.
      now apply NonnegativeRationals_leplus_l. }
    set (cx := ((c / 2) / (y + (c / 2)))%NRat).
    assert (Hcx0 : (0 < cx)%NRat)
      by (now apply ispositive_divNonnegativeRationals).
    generalize (X_error _ Hcx0) ; apply hinhfun ; intros [H | H].
    + left.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
      intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
      revert Hz.
      apply gtNonnegativeRationals_noteq.
      apply istrans_ltNonnegativeRationals with (c / 2)%NRat.
      rewrite <- (multdivNonnegativeRationals (c / 2)%NRat (y + (c / 2)%NRat)).
      rewrite iscomm_multNonnegativeRationals.
      apply multNonnegativeRationals_lt.
      apply notge_ltNonnegativeRationals ; intro H0.
      now apply nYy, Y_bot with (1 := Yr).
      apply notge_ltNonnegativeRationals ; intro H0.
      apply H, X_bot with (1 := Xr).
      exact H0.
      exact Hq1.
      rewrite <- (islunit_zeroNonnegativeRationals (c / 2)%NRat).
      pattern c at 2 ; rewrite (NQhalf_double c).
      now rewrite plusNonnegativeRationals_ltcompat_r.
    + right.
      revert H ; apply hinhfun ; intros (x,(Xx,nXx)).
      exists (x * y) ; repeat split.
      * apply hinhpr.
        exists (x,y) ; simpl ; now repeat split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
        intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
        revert Hz.
        apply gtNonnegativeRationals_noteq.
        apply istrans_lt_le_ltNonnegativeRationals with ((x + cx)* (y + (c / 2)%NRat)).
        apply multNonnegativeRationals_lt.
        apply notge_ltNonnegativeRationals.
        now intros H ; apply nXx, X_bot with (1 := Xr).
        apply notge_ltNonnegativeRationals.
        now intros H ; apply nYy, Y_bot with (1 := Yr).
        rewrite isrdistr_mult_plusNonnegativeRationals, (iscomm_multNonnegativeRationals cx).
        unfold cx ; rewrite multdivNonnegativeRationals.
        pattern c at 3 ;
          rewrite (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
        apply NonnegativeRationals_pluslecompat_r.
        rewrite isldistr_mult_plusNonnegativeRationals.
        apply NonnegativeRationals_pluslecompat_l.
        rewrite iscomm_multNonnegativeRationals.
        apply multrle1NonnegativeRationals.
        apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
        intro H ; apply Hx1.
        now apply X_bot with (1 := Xx).
        exact Hq1.
Qed.

End Dcuts_mult.

Section Dcuts_mult'.

  Context (X : hsubtypes NonnegativeRationals).
  Context (X_bot : Dcuts_def_bot X).
  Context (X_open : Dcuts_def_open X).
  Context (X_finite : Dcuts_def_finite X).
  Context (X_error : Dcuts_def_error X).
  Context (Y : hsubtypes NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_finite : Dcuts_def_finite Y).
  Context (Y_error : Dcuts_def_error Y).

Lemma Dcuts_mult_error : Dcuts_def_error (Dcuts_mult_val X Y).
Proof.
  intros c Hc.
  generalize (X_error 1%NRat ispositive_oneNonnegativeRationals).
  apply hinhuniv ; intros [Hx1 | Hx].
  - now apply Dcuts_mult_error_aux.
  - revert Hx ; apply hinhuniv ; intros (x,(Xx,nXx)).
    assert (Hx1 : (0 < x + 1)%NRat).
    { apply istrans_lt_le_ltNonnegativeRationals with (1 := ispositive_oneNonnegativeRationals).
      apply NonnegativeRationals_leplus_l. }
    assert (Heq : Dcuts_mult_val X Y = (Dcuts_NQmult_val (x + 1%NRat) (Dcuts_mult_val (Dcuts_NQmult_val (/ (x + 1))%NRat X) Y))).
    { apply funextfun ; intro r.
      apply uahp.
      - apply hinhfun ; intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr)).
        exists (r / (x + 1))%NRat ; split.
        + now  rewrite multdivNonnegativeRationals.
        + apply hinhpr.
          exists (rx / (x + 1%NRat),ry)%NRat ; simpl ; repeat split.
          * unfold divNonnegativeRationals.
            rewrite isassoc_multNonnegativeRationals, (iscomm_multNonnegativeRationals (/ (x + 1))%NRat).
            now rewrite <- isassoc_multNonnegativeRationals, Hr.
          * apply hinhpr.
            exists rx ; split.
            now apply iscomm_multNonnegativeRationals.
            exact Xr.
          * exact Yr.
      - apply hinhuniv ; intros (rx,(Hr)).
        apply hinhuniv ; intros ((rx',ry),(Hrx,(H,Yr))) ; simpl in Hrx, Yr.
        revert H ; apply hinhfun ; intros (rx'',(Hrx',Xrx)) ; simpl in Hrx'.
        rewrite Hrx' in Hrx ; clear rx' Hrx'.
        rewrite Hrx in Hr ; clear rx Hrx.
        rewrite <- !isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals in Hr.
        exists (rx'',ry) ; now repeat split.
        exact Hx1.
    }
    rewrite Heq.
    revert c Hc.
    apply Dcuts_NQmult_error.
    + exact Hx1.
    + apply Dcuts_mult_bot, Y_bot.
      now apply Dcuts_NQmult_bot.
    + apply Dcuts_mult_error_aux.
      now apply Dcuts_NQmult_bot.
      apply Dcuts_NQmult_error.
      now rewrite invNonnegativeRationals_pos.
      exact X_bot.
      exact X_error.
      exact Y_bot.
      exact Y_error.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
      intros (rx,(Hz,Xr)) ; simpl in Hz,Xr.
      apply nXx, X_bot with (1 := Xr).
      rewrite <- (isrunit_oneNonnegativeRationals (x + 1%NRat)).
      pattern 1%NRat at 2 ; rewrite Hz, <- isassoc_multNonnegativeRationals.
      rewrite isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
      now apply isrefl_leNonnegativeRationals.
      exact Hx1.
Qed.

End Dcuts_mult'.

Definition Dcuts_mult (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_mult_val (pr1 X) (pr1 Y))
           (Dcuts_mult_bot (pr1 X) (is_Dcuts_bot X)
                           (pr1 Y) (is_Dcuts_bot Y))
           (Dcuts_mult_open (pr1 X) (is_Dcuts_open X)
                            (pr1 Y) (is_Dcuts_open Y))
           (Dcuts_mult_error (pr1 X) (is_Dcuts_bot X) (is_Dcuts_error X)
                             (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_error Y)).

(** ** Multiplicative inverse in Dcuts *)

Section Dcuts_inv.

Context (X : hsubtypes NonnegativeRationals).
Context (X_bot : Dcuts_def_bot X).
Context (X_open : Dcuts_def_open X).
Context (X_finite : Dcuts_def_finite X).
Context (X_error : Dcuts_def_error X).
Context (X_0 : X 0%NRat).

Definition Dcuts_inv_val : hsubtypes NonnegativeRationals :=
  λ r : NonnegativeRationals,
        hexists (λ l : NonnegativeRationals, (∀ rx : NonnegativeRationals, X rx -> (r * rx <= l)%NRat)
                                               × (0 < l)%NRat × (l < 1)%NRat).

Local Lemma Dcuts_inv_in :
  ∀ x, (0 < x)%NRat -> X x -> (Dcuts_inv_val (/ x)%NRat) -> empty.
Proof.
  intros x Hx0 Xx.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (l,(H,(Hl0,Hl1))).
  specialize (H _ Xx).
  rewrite islinv_NonnegativeRationals in H.
  revert H Hl1.
  now apply EOle_not_EOlt.
  exact Hx0.
Qed.
Local Lemma Dcuts_inv_out :
  ∀ x, ¬ (X x) -> forall y, (x < y)%NRat -> Dcuts_inv_val (/ y)%NRat.
Proof.
  intros x nXx y Hy.
  apply hinhpr.
  exists (x / y)%NRat ; repeat split.
  - intros rx Hrx.
    unfold divNonnegativeRationals.
    rewrite iscomm_multNonnegativeRationals.
    apply multNonnegativeRationals_le_r'.
    apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
    intros H ; apply nXx.
    now apply X_bot with (1 := Hrx).
  - apply ispositive_divNonnegativeRationals.
    apply notge_ltNonnegativeRationals.
    intros H ; apply nXx.
    now apply X_bot with (1 := X_0).
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
  - rewrite <- (multNonnegativeRationals_lt_r y).
    unfold divNonnegativeRationals.
    rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals.
    exact Hy.
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
Qed.

Lemma Dcuts_inv_bot : Dcuts_def_bot Dcuts_inv_val.
Proof.
  intros r Hr q Hq.
  revert Hr.
  apply hinhfun ; intros (l,(Hr,(Hl0,Hl1))).
  exists l ; repeat split.
  - intros rx Xrx.
    apply istrans_leNonnegativeRationals with (2 := Hr _ Xrx).
    now apply multNonnegativeRationals_le_r'.
  - exact Hl0.
  - exact Hl1.
Qed.

Lemma Dcuts_inv_open : Dcuts_def_open Dcuts_inv_val.
Proof.
  intros r.
  apply hinhuniv.
  intros (l,(Hr,(Hl0,Hl1))).
  destruct (eq0orgt0NonnegativeRationals r) as [Hr0 | Hr0].
  - rewrite Hr0 ; clear r Hr0 Hr.
    revert X_finite.
    apply hinhfun.
    intros (r',Hr').
    set (r := NQmax 2%NRat r').
    assert (Hr1 : (1 < r)%NRat).
    { apply istrans_lt_le_ltNonnegativeRationals with (2 := NQmax_le_l _ _).
      exact one_lt_twoNonnegativeRationals. }
    assert (Hr0 : (0 < r)%NRat).
    { apply istrans_le_lt_ltNonnegativeRationals with (2 := Hr1).
      now apply isnonnegative_NonnegativeRationals. }
    exists (/ (r * r))%NRat ; split.
    + apply hinhpr.
      exists (/ r)%NRat ; repeat split.
      * intros rx Xrx.
        rewrite <- (multNonnegativeRationals_le_l (r * r)).
        rewrite <- isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        rewrite isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (2 := NQmax_le_r _ _).
        apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals ; intro H ; apply Hr'.
        now apply X_bot with (1 := Xrx).
        exact Hr0.
        now apply ispositive_multNonnegativeRationals.
        now apply ispositive_multNonnegativeRationals.
      * now rewrite invNonnegativeRationals_pos.
      * now rewrite <- (multNonnegativeRationals_lt_l r), isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
    + rewrite invNonnegativeRationals_pos.
      now apply ispositive_multNonnegativeRationals.
  - apply between_ltNonnegativeRationals in Hl1.
    destruct Hl1 as [l' (Hl',Hl'1)].
    apply hinhpr.
    exists ((l'/l) * r)%NRat ; split.
    + apply hinhpr.
      exists l' ; repeat split.
      * intros rx Xrx.
        rewrite isassoc_multNonnegativeRationals.
        pattern l' at 2 ;
          rewrite <- (multdivNonnegativeRationals l' l), iscomm_multNonnegativeRationals.
        apply multNonnegativeRationals_le_r'.
        now apply Hr.
        exact Hl0.
      * apply istrans_le_lt_ltNonnegativeRationals with (2 := Hl').
        now apply isnonnegative_NonnegativeRationals.
      * exact Hl'1.
    + pattern r at 1 ; rewrite <- (islunit_oneNonnegativeRationals r).
      rewrite multNonnegativeRationals_lt_r, <- (multNonnegativeRationals_lt_r l _ _ Hl0), islunit_oneNonnegativeRationals.
      now rewrite iscomm_multNonnegativeRationals, multdivNonnegativeRationals.
      exact Hr0.
Qed.

Context (X_1 : X 1%NRat).

Lemma Dcuts_inv_error_aux : Dcuts_def_error Dcuts_inv_val.
Proof.
  assert (forall c, (0 < c)%NRat -> hexists (λ q : NonnegativeRationals, X q × ¬ X (q + c))).
  { intros c Hc0.
    generalize (X_error c Hc0) ; apply hinhuniv ; intros [nXc | H].
    - apply hinhpr.
      exists 0%NRat ; split.
      + exact X_0.
      + now rewrite islunit_zeroNonnegativeRationals.
    - exact H. }
  clear X_error ; rename X0 into X_error.

  intros c Hc0.
  apply hinhpr ; right.
  rewrite NQhalf_is_pos in Hc0.
  specialize (X_error _ Hc0) ; revert X_error.
  apply hinhfun ; intros (r,(Xr,nXr)).
  exists (/ (NQmax 1%NRat r + c))%NRat ; split.
  - apply Dcuts_inv_out with (1 := nXr).
    pattern c at 2 ; rewrite (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
    eapply istrans_le_lt_ltNonnegativeRationals, NonnegativeRationals_ltplus_r.
    apply NonnegativeRationals_pluslecompat_r, NQmax_le_r.
    exact Hc0.
  - assert (Xmax : X (NQmax 1%NRat r)) by (now apply NQmax_case).
    assert (Hmax : (0 < NQmax 1 r)%NRat).
    { eapply istrans_lt_le_ltNonnegativeRationals, NQmax_le_l.
      now eapply ispositive_oneNonnegativeRationals. }
    intro Hinv ; apply (Dcuts_inv_in _ Hmax Xmax), Dcuts_inv_bot with (1 := Hinv).
    apply lt_leNonnegativeRationals, minus_ltNonnegativeRationals_l' with (/ (NQmax 1 r + c))%NRat.
    rewrite NonnegativeRationals_plusl_minus.
    rewrite minus_divNonnegativeRationals, NonnegativeRationals_plusl_minus.
    unfold divNonnegativeRationals ;
    rewrite <- (multNonnegativeRationals_lt_r (NQmax 1 r * (NQmax 1 r + c))%NRat), isassoc_multNonnegativeRationals, islinv_NonnegativeRationals.
    rewrite multNonnegativeRationals_lt_l.
    pattern 1%NRat at 1 ;
      rewrite <- (islunit_oneNonnegativeRationals 1%NRat).
    apply istrans_le_lt_ltNonnegativeRationals with (NQmax 1 r * 1)%NRat.
    now apply multNonnegativeRationals_le_r', NQmax_le_l.
    rewrite multNonnegativeRationals_lt_l.
    apply istrans_le_lt_ltNonnegativeRationals with (1 := NQmax_le_l _ r).
    apply NonnegativeRationals_ltplus_r.
    now rewrite NQhalf_is_pos.
    exact Hmax.
    now rewrite NQhalf_is_pos.
    apply ispositive_multNonnegativeRationals.
    exact Hmax.
    now apply ispositive_plusNonnegativeRationals_l.
    apply ispositive_multNonnegativeRationals.
    exact Hmax.
    now apply ispositive_plusNonnegativeRationals_l.
    now apply ispositive_plusNonnegativeRationals_l.
Qed.

End Dcuts_inv.

Section Dcuts_inv'.

Context (X : hsubtypes NonnegativeRationals).
Context (X_bot : Dcuts_def_bot X).
Context (X_open : Dcuts_def_open X).
Context (X_finite : Dcuts_def_finite X).
Context (X_error : Dcuts_def_error X).
Context (X_0 : X 0%NRat).

Lemma Dcuts_inv_error : Dcuts_def_error (Dcuts_inv_val X).
Proof.
  generalize (X_open _ X_0) ; apply (hinhuniv (P := hProppair _ (isaprop_Dcuts_def_error _))) ; intros (x,(Xx,Hx0)) ; simpl.
  set (Y := Dcuts_NQmult_val (/ x)%NRat X).
  assert (Y_1 : Y 1%NRat).
  { unfold Y ; apply hinhpr ; exists x ; split.
    now rewrite islinv_NonnegativeRationals.
    exact Xx. }
  assert (Heq : Dcuts_inv_val X = Dcuts_NQmult_val (/x)%NRat (Dcuts_inv_val Y)).
  { apply funextfun ; intro r.
    apply uahp.
    - apply hinhfun ; intros (l,(Hl,(Hl0,Hl1))).
      exists (x * r) ; split.
      now rewrite <- isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
      apply hinhpr.
      exists l ; repeat split.
      intros q ; unfold Y.
      apply hinhuniv ; intros (s,(->,Xs)).
      rewrite (iscomm_multNonnegativeRationals x), <- isassoc_multNonnegativeRationals.
      rewrite iscomm_multNonnegativeRationals, !isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals, iscomm_multNonnegativeRationals.
      now apply Hl.
      exact Hx0.
      exact Hl0.
      exact Hl1.
    - apply hinhuniv ; intros (q,(->)).
      apply hinhfun ; intros (l,(Hl,(Hl0,Hl1))).
      exists l ; repeat split.
      intros s Xs.
      rewrite (iscomm_multNonnegativeRationals (/ x)%NRat), isassoc_multNonnegativeRationals.
      apply Hl.
      unfold Y ; apply hinhpr.
      now exists s.
      exact Hl0.
      exact Hl1. }
  rewrite Heq.
  apply Dcuts_NQmult_error.
  now rewrite invNonnegativeRationals_pos.
  now apply Dcuts_inv_bot.
  apply Dcuts_inv_error_aux.
  now unfold Y ; apply Dcuts_NQmult_bot.
  unfold Y ; apply Dcuts_NQmult_error.
  now rewrite invNonnegativeRationals_pos.
  exact X_bot.
  exact X_error.
  apply hinhpr ; exists 0%NRat ; split.
  now rewrite israbsorb_zero_multNonnegativeRationals.
  exact X_0.
  exact Y_1.
Qed.

End Dcuts_inv'.

Definition Dcuts_inv (X : Dcuts) (X_0 : X # 0) : Dcuts.
Proof.
  intros.
  apply (mk_Dcuts (Dcuts_inv_val (pr1 X))).
  - now apply Dcuts_inv_bot.
  - apply Dcuts_inv_open.
    now apply is_Dcuts_bot.
    now apply Dcuts_def_error_finite, is_Dcuts_error.
  - apply Dcuts_inv_error.
    now apply is_Dcuts_bot.
    now apply is_Dcuts_open.
    now apply is_Dcuts_error.
    now rewrite <- Dcuts_apzero_notempty.
Defined.

(** ** Algebraic properties *)

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

Lemma Dcuts_plus_lt_l :
  ∀ x x' y : Dcuts, Dcuts_plus x y < Dcuts_plus x' y -> x < x'.
Proof.
  intros x x' y.
  apply hinhuniv ; intros (r,(Nr,Hr)).
  revert Hr ; apply hinhuniv ; intros [ | ] ; apply hinhfun ;
  [ intros [Xr | Yr] | intros ((rx,ry),(Hr,(Xr,Yr))) ].
  - exists r ; split.
    intro H ; apply Nr.
    apply hinhpr ; left.
    now apply hinhpr ; left.
    exact Xr.
  - apply fromempty, Nr.
    apply hinhpr ; left.
    now apply hinhpr ; right.
  - simpl in Hr,Xr,Yr.
    exists rx ; split.
    intro H ; apply Nr.
    apply hinhpr ; right.
    now apply hinhpr ; exists (rx,ry).
    exact Xr.
Qed.

Lemma islapbinop_Dcuts_plus : islapbinop Dcuts_plus.
Proof.
  intros y x x'.
  apply hinhfun ; intros [Hlt | Hlt].
  - left.
    now apply Dcuts_plus_lt_l with y.
  - right.
    now apply Dcuts_plus_lt_l with y.
Qed.
Lemma israpbinop_Dcuts_plus : israpbinop Dcuts_plus.
Proof.
  intros x y y'.
  rewrite !(iscomm_Dcuts_plus x).
  now apply islapbinop_Dcuts_plus.
Qed.

Lemma iscomm_Dcuts_mult : iscomm Dcuts_mult.
Proof.
  intros x y.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhfun ; intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr)).
    exists (ry,rx) ; repeat split.
    now rewrite iscomm_multNonnegativeRationals.
    exact Yr.
    exact Xr.
  - apply hinhfun ; intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr)).
    exists (ry,rx) ; repeat split.
    now rewrite iscomm_multNonnegativeRationals.
    exact Yr.
    exact Xr.
Qed.

Lemma Dcuts_mult_lt_l :
  ∀ x x' y : Dcuts, Dcuts_mult x y < Dcuts_mult x' y -> x < x'.
Proof.
  intros x x' y.
  apply hinhuniv ; intros (r,(Nr)).
  apply hinhfun ; intros ((rx,ry),(Hr,(Xr,Yr))).
  simpl in Hr,Xr,Yr.
  exists rx ; split.
  intro H ; apply Nr.
  now apply hinhpr ; exists (rx,ry).
  exact Xr.
Qed.
Lemma islapbinop_Dcuts_mult : islapbinop Dcuts_mult.
Proof.
  intros y x x'.
  apply hinhfun ; intros [Hlt | Hlt].
  - left.
    now apply Dcuts_mult_lt_l with y.
  - right.
    now apply Dcuts_mult_lt_l with y.
Qed.
Lemma israpbinop_Dcuts_mult : israpbinop Dcuts_mult.
Proof.
  intros x y y'.
  rewrite !(iscomm_Dcuts_mult x).
  now apply islapbinop_Dcuts_mult.
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
Lemma isassoc_Dcuts_mult : isassoc Dcuts_mult.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((rxy,rz)) ; simpl ; intros (Hr,(XYr,Zr)) ; revert XYr.
    apply hinhfun ; intros ((rx,ry)) ; simpl ; intros (Hrxy,(Xr,Yr)).
    rewrite Hrxy, isassoc_multNonnegativeRationals in Hr ; clear rxy Hrxy.
    exists (rx,(ry * rz)) ; simpl ; repeat split.
    + exact Hr.
    + exact Xr.
    + now  apply hinhpr ; exists (ry,rz).
  - apply hinhuniv ; intros ((rx,ryz)) ; simpl ; intros (Hr,(Xr)).
    apply hinhfun ; intros ((ry,rz)) ; simpl ; intros (Hryz,(Yr,Zr)).
    rewrite Hryz, <- isassoc_multNonnegativeRationals in Hr ; clear ryz Hryz.
    exists ((rx * ry) , rz) ; simpl ; repeat split.
    + exact Hr.
    + now  apply hinhpr ; exists (rx,ry).
    + exact Zr.
Qed.
Lemma islunit_Dcuts_mult_one : islunit Dcuts_mult Dcuts_one.
Proof.
  intros x.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((ri,rx),(Hr,(Ir,Xr))).
    apply is_Dcuts_bot with (1 := Xr).
    rewrite Hr, iscomm_multNonnegativeRationals.
    now apply multrle1NonnegativeRationals, lt_leNonnegativeRationals.
  - intros Xr.
    generalize (is_Dcuts_open x r Xr).
    apply hinhfun ; intros (q,(Xq,Hrq)).
    exists ((r/q)%NRat,q) ; repeat split.
    + simpl.
      rewrite iscomm_multNonnegativeRationals, multdivNonnegativeRationals.
      reflexivity.
      apply istrans_le_lt_ltNonnegativeRationals with (2 := Hrq).
      apply isnonnegative_NonnegativeRationals.
    +  change (r / q < 1)%NRat.
       rewrite <- (multNonnegativeRationals_lt_l q), multdivNonnegativeRationals, isrunit_oneNonnegativeRationals.
       exact Hrq.
       apply istrans_le_lt_ltNonnegativeRationals with (2 := Hrq).
       apply isnonnegative_NonnegativeRationals.
       apply istrans_le_lt_ltNonnegativeRationals with (2 := Hrq).
       apply isnonnegative_NonnegativeRationals.
    + exact Xq.
Qed.
Lemma isrunit_Dcuts_mult_one : isrunit Dcuts_mult Dcuts_one.
Proof.
  intros x.
  rewrite iscomm_Dcuts_mult.
  now apply islunit_Dcuts_mult_one.
Qed.
Lemma islabsorb_Dcuts_mult_zero :
  ∀ x : Dcuts, Dcuts_mult Dcuts_zero x = Dcuts_zero.
Proof.
  intros x.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((ri,rx),(Hr,(Or,Xr))).
    now rewrite Dcuts_zero_empty in Or |- *.
  - rewrite Dcuts_zero_empty.
    now apply fromempty.
Qed.
Lemma israbsorb_Dcuts_mult_zero :
  ∀ x : Dcuts, Dcuts_mult x Dcuts_zero = Dcuts_zero.
Proof.
  intros x.
  rewrite iscomm_Dcuts_mult.
  now apply islabsorb_Dcuts_mult_zero.
Qed.
Lemma isldistr_Dcuts_plus_mult : isldistr Dcuts_plus Dcuts_mult.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((rz,rxy),(Hr,(Zr))) ; simpl in Hr, Zr.
    apply hinhuniv ; intros [|] ; apply hinhfun ;
    [ intros [Xr|Yr] ; [simpl in Xr| simpl in Yr]
    | intros ((rx,ry),(Hrxy,(Xr,Yr))) ; simpl in Hrxy,Xr,Yr].
    + left ; apply hinhpr.
      left ; apply hinhpr.
      exists (rz,rxy) ; now repeat split.
    + left ; apply hinhpr.
      right ; apply hinhpr.
      exists (rz,rxy) ; now repeat split.
    + rewrite Hrxy, isldistr_mult_plusNonnegativeRationals in Hr ; clear rxy Hrxy.
      right ; apply hinhpr.
      exists (rz * rx, rz * ry) ; simpl ; repeat split.
      * exact Hr.
      * now apply hinhpr ; exists (rz,rx).
      * now apply hinhpr ; exists (rz,ry).
  - apply hinhuniv ; intros [|] ; apply hinhuniv ;
    [ intros [|]
    | intros ((rzx,rzy),(Hr,())) ; simpl in Hr ].
    + apply hinhfun ; intros ((rz,rx)) ; simpl ; intros (Hr,(Zr,XYr)).
      exists (rz,rx) ; simpl ; repeat split.
      * exact Hr.
      * exact Zr.
      * apply hinhpr ; left.
        now apply hinhpr ; left.
    + apply hinhfun ; intros ((rz,ry)) ; simpl ; intros (Hr,(Zr,Yr)).
      exists (rz,ry) ; simpl ; repeat split.
      * exact Hr.
      * exact Zr.
      * apply hinhpr ; left.
        now apply hinhpr ; right.
    + apply hinhfun2 ; intros ((zx,rx),(Hzx,(Zrx,Xr))) ((zy,ry),(Hzy,(Zry,Yr))) ;
      simpl in * |- .
      destruct (isdecrel_leNonnegativeRationals (NQmax zx zy) 0%NRat) as [Heq|Hlt].
      rewrite <- NonnegativeRationals_eq0_le0 in Heq.
      * apply NQmax_eq_zero in Heq ; destruct Heq as [Hx Hy].
        exists (0%NRat,rx) ; simpl ; repeat split.
        rewrite Hr, Hzx, Hzy, Hx,Hy, !islabsorb_zero_multNonnegativeRationals.
        now apply isrunit_zeroNonnegativeRationals.
        now rewrite <- Hx.
        apply hinhpr ; left.
        now apply hinhpr ; left.
      * apply notge_ltNonnegativeRationals in Hlt.
        exists (NQmax zx zy, (rzx / NQmax zx zy)%NRat + (rzy / NQmax zx zy)%NRat) ;
          simpl ; repeat split.
        unfold divNonnegativeRationals.
        rewrite <- isrdistr_mult_plusNonnegativeRationals, <- Hr.
        change (r * (/ NQmax zx zy)%NRat) with (r / NQmax zx zy)%NRat.
        now rewrite multdivNonnegativeRationals.
        now apply NQmax_case.
        apply hinhpr ; right.
        apply hinhpr.
        exists ((rzx / NQmax zx zy)%NRat , (rzy / NQmax zx zy)%NRat) ; simpl ; repeat split.
        apply is_Dcuts_bot with (1 := Xr).
        rewrite Hzx, iscomm_multNonnegativeRationals.
        unfold divNonnegativeRationals ;
          rewrite isassoc_multNonnegativeRationals.
        apply multrle1NonnegativeRationals, ledivle1NonnegativeRationals.
        now apply NQmax_le_l.
        apply is_Dcuts_bot with (1 := Yr).
        rewrite Hzy, iscomm_multNonnegativeRationals.
        unfold divNonnegativeRationals ;
          rewrite isassoc_multNonnegativeRationals.
        apply multrle1NonnegativeRationals, ledivle1NonnegativeRationals.
        now apply NQmax_le_r.
Qed.
Lemma isrdistr_Dcuts_plus_mult : isrdistr Dcuts_plus Dcuts_mult.
Proof.
  intros x y z.
  rewrite <- ! (iscomm_Dcuts_mult z).
  now apply isldistr_Dcuts_plus_mult.
Qed.

Definition Dcuts_ap_one_zero : 1 # 0.
Proof.
  apply isapfun_NonnegativeRationals_to_Dcuts'.
  apply gtNonnegativeRationals_noteq.
  exact ispositive_oneNonnegativeRationals.
Qed.
Lemma multNonnegativeRationals_le_lt:
  ∀ x x' y y' : NonnegativeRationals,
  (0 < x)%NRat -> (x <= x')%NRat -> (y < y')%NRat -> (x * y < x' * y')%NRat.
Admitted.
Lemma minus_ltNonnegativeRationals_l:
  ∀ x y z : NonnegativeRationals, (x < y)%NRat -> (z < y)%NRat -> (x - z < y - z)%NRat.
Admitted.
Definition islinv_Dcuts_inv :
  ∀ x : Dcuts, forall Hx0 : x # 0, Dcuts_mult (Dcuts_inv x Hx0) x = 1.
Proof.
  intros x Hx0.
  apply Dcuts_eq_is_eq ; intro q ; split.
  - apply hinhuniv ; intros ((r,s),(->,(Hr,Hs))) ; revert Hr ; simpl in Hs.
    apply hinhuniv ; intros (l,(Hl,(Hl0,Hl1))).
    change (r * s < 1)%NRat.
    apply istrans_le_lt_ltNonnegativeRationals with l.
    now apply Hl, Hs.
    exact Hl1.
  - change (q ∈ 1) with (q < 1)%NRat ; intro Hq.
    generalize Hx0 ; intro Hx.
    rewrite Dcuts_apzero_notempty in Hx0.
    destruct (eq0orgt0NonnegativeRationals q) as [Hq0 | Hq0].
    + rewrite Hq0.
      apply hinhpr.
      exists (0%NRat,0%NRat) ; repeat split.
      * simpl ; now rewrite islabsorb_zero_multNonnegativeRationals.
      * apply hinhpr.
        exists (/ 2)%NRat ; split.
        simpl fst ; intros.
        rewrite islabsorb_zero_multNonnegativeRationals.
        now apply isnonnegative_NonnegativeRationals.
        split.
        rewrite invNonnegativeRationals_pos.
        exact ispositive_twoNonnegativeRationals.
        rewrite <- (multNonnegativeRationals_lt_l 2), isrunit_oneNonnegativeRationals, isrinv_NonnegativeRationals.
        exact one_lt_twoNonnegativeRationals.
        exact ispositive_twoNonnegativeRationals.
        exact ispositive_twoNonnegativeRationals.
      * exact Hx0.
    + generalize (is_Dcuts_open _ _ Hx0).
      apply hinhuniv ; intros (r,(Xr,Hr0)).
      apply between_ltNonnegativeRationals in Hq.
      destruct Hq as [t (Ht,Ht1)].
      set (c := r * (/ t - 1)%NRat).
      assert (Hc0 : (0 < c)%NRat).
      { unfold c.
        apply ispositive_multNonnegativeRationals.
        exact Hr0.
        rewrite minusNonnegativeRationals_gt0.
        rewrite <- (multNonnegativeRationals_lt_l t), isrunit_oneNonnegativeRationals, isrinv_NonnegativeRationals.
        exact Ht1.
        now apply istrans_ltNonnegativeRationals with q.     now apply istrans_ltNonnegativeRationals with q. }
      generalize (Dcuts_def_error_not_empty _ Hx0 (is_Dcuts_error x) _ Hc0).
      apply hinhfun ; intros (r',(Xr',nXr')).
      exists ((q * / (NQmax r r'))%NRat,NQmax r r') ; repeat split.
      * simpl.
        rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        reflexivity.
        apply istrans_lt_le_ltNonnegativeRationals with r.
        exact Hr0.
        now apply NQmax_le_l.
      * apply hinhpr ; simpl fst.
        exists (q / NQmax r r' * (NQmax r r' + c))%NRat.
        repeat split.
        intros rx Xrx.
        apply multNonnegativeRationals_le_l', lt_leNonnegativeRationals.
        apply (Dcuts_finite x).
        intro H ; apply nXr'.
        apply is_Dcuts_bot with (1 := H).
        now apply NonnegativeRationals_pluslecompat_r, NQmax_le_r.
        exact Xrx.
        apply ispositive_multNonnegativeRationals.
        apply ispositive_divNonnegativeRationals.
        exact Hq0.
        apply istrans_lt_le_ltNonnegativeRationals with r.
        exact Hr0.
        now apply NQmax_le_l.
        rewrite iscomm_plusNonnegativeRationals.
        now apply ispositive_plusNonnegativeRationals_l.
        unfold divNonnegativeRationals.
        rewrite <- (multNonnegativeRationals_lt_l (/ q)%NRat), isrunit_oneNonnegativeRationals, <- !isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        2: exact Hq0.
        2: now rewrite invNonnegativeRationals_pos.
        rewrite <- (multNonnegativeRationals_lt_l (NQmax r r')), <- !isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        2: apply istrans_lt_le_ltNonnegativeRationals with r.
        2: exact Hr0.
        2: now apply NQmax_le_l.
        2: apply istrans_lt_le_ltNonnegativeRationals with r.
        2: exact Hr0.
        2: now apply NQmax_le_l.
        apply (minus_ltNonnegativeRationals_l' _ _ (NQmax r r' * 1)%NRat).
        rewrite <- isldistr_mult_minusNonnegativeRationals, isrunit_oneNonnegativeRationals, NonnegativeRationals_plusl_minus.
        unfold c.
        apply multNonnegativeRationals_le_lt.
        exact Hr0.
        now apply NQmax_le_l.
        rewrite <- (multNonnegativeRationals_lt_l q), !isldistr_mult_minusNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        2: exact Hq0.
        2: exact Hq0.
        rewrite <- (multNonnegativeRationals_lt_r t), !isrdistr_mult_minusNonnegativeRationals, isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals, islunit_oneNonnegativeRationals.
        2: now apply istrans_ltNonnegativeRationals with q.
        2: now apply istrans_ltNonnegativeRationals with q.
        apply minus_ltNonnegativeRationals_l.
        exact Ht.
        pattern t at 2 ;
          rewrite <- (islunit_oneNonnegativeRationals t).
        rewrite multNonnegativeRationals_lt_r.
        now apply istrans_ltNonnegativeRationals with t.
        now apply istrans_ltNonnegativeRationals with q.
      * simpl.
        now apply NQmax_case.
Qed.
Definition isrinv_Dcuts_inv :
  ∀ x : Dcuts, forall Hx0 : x # 0, Dcuts_mult x (Dcuts_inv x Hx0) = 1.
Proof.
  intros x Hx0.
  rewrite iscomm_Dcuts_mult.
  now apply islinv_Dcuts_inv.
Qed.

(** ** Structures *)

Definition Dcuts_apsetwith2binop : apsetwith2binop.
Proof.
  exists Dcuts.
  split.
  - exists Dcuts_plus ; repeat split.
    exact islapbinop_Dcuts_plus.
    exact israpbinop_Dcuts_plus.
  - exists Dcuts_mult ; repeat split.
    exact islapbinop_Dcuts_mult.
    exact israpbinop_Dcuts_mult.
Defined.

Definition isabmonoidop_Dcuts_plus : isabmonoidop Dcuts_plus.
Proof.
  repeat split.
  - exact isassoc_Dcuts_plus.
  - exists Dcuts_zero.
    split.
    + exact islunit_Dcuts_plus_zero.
    + exact isrunit_Dcuts_plus_zero.
  - exact iscomm_Dcuts_plus.
Defined.

Definition ismonoidop_Dcuts_mult : ismonoidop Dcuts_mult.
Proof.
  split.
  - exact isassoc_Dcuts_mult.
  - exists Dcuts_one.
    split.
    + exact islunit_Dcuts_mult_one.
    + exact isrunit_Dcuts_mult_one.
Defined.
Definition Dcuts_ConstructiveCommutativeRig : ConstructiveCommutativeRig.
Proof.
  exists Dcuts_apsetwith2binop.
  repeat split.
  - exists (isabmonoidop_Dcuts_plus,,ismonoidop_Dcuts_mult).
    split.
    + exact islabsorb_Dcuts_mult_zero.
    + exact israbsorb_Dcuts_mult_zero.
  - exact isldistr_Dcuts_plus_mult.
  - exact isrdistr_Dcuts_plus_mult.
  - exact iscomm_Dcuts_mult.
Defined.
Definition Dcuts_ConstructiveDivisionRig : ConstructiveDivisionRig.
Proof.
  exists Dcuts_ConstructiveCommutativeRig.
  split.
  - exact Dcuts_ap_one_zero.
  - intros x Hx.
    exists (Dcuts_inv x Hx) ; split.
    + exact (islinv_Dcuts_inv x Hx).
    + exact (isrinv_Dcuts_inv x Hx).
Defined.

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

Lemma ispreorder_Dcuts_le_rel : ispreorder Dcuts_le_rel.
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
    + exact ispreorder_Dcuts_le_rel.
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

<<<<<<< HEAD
Context (E : hsubtypes Dcuts).
Context (E_not_empty : hexists E).

Definition Dcuts_glb_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun n => dirprod (r < n)%NRat (forall X : Dcuts, E X -> n ∈ X)).
=======
Context (E : subset Dcuts).
Context (E_not_empty : hexists E).

Definition Dcuts_glb_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (fun n => dirprod (r < n)%NnR (forall X : Dcuts, E X -> n ∈ X)).
>>>>>>> apartness
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