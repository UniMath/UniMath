(** * Definition of Dedekind cuts for non-negative real numbers *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Sets.
Require Export UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.NonnegativeRationals.

Delimit Scope Dcuts_scope with Dcuts.
Local Open Scope NRat_scope.
Local Open Scope Dcuts_scope.
Local Open Scope tap_scope.

(** ** Definition of Dedekind cuts *)

Definition Dcuts_def_bot (X : hsubtypes NonnegativeRationals) : UU :=
  Π x : NonnegativeRationals, X x ->
    Π y : NonnegativeRationals, y <= x -> X y.
Definition Dcuts_def_open (X : hsubtypes NonnegativeRationals) : UU :=
  Π x : NonnegativeRationals, X x ->
    hexists (fun y : NonnegativeRationals => (X y) × (x < y)).
Definition Dcuts_def_finite (X : hsubtypes NonnegativeRationals) : hProp :=
  ∃ ub : NonnegativeRationals, ¬ (X ub).
Definition Dcuts_def_error (X : hsubtypes NonnegativeRationals) : UU :=
  Π r : NonnegativeRationals, 0 < r -> (¬ (X r)) ∨ Σ q : NonnegativeRationals, (X q) × (¬ (X (q + r))).
Definition Dcuts_def_error' (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) : UU :=
  Π r, 0 < r -> r <= k -> (¬ (X r)) ∨ Σ q : NonnegativeRationals, (0 < q) × (X q) × (¬ (X (q + r))).

Lemma Dcuts_def_error'_correct1 (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) :
  Dcuts_def_bot X -> Dcuts_def_open X ->
  Dcuts_def_error X -> Dcuts_def_error' X k.
Proof.
  intros X k Hbot Hopen H r Hr0 _.
  generalize (H r Hr0) ; clear H.
  apply hinhuniv ; intros [H | H].
  - apply hinhpr ; now left.
  - destruct H as (q,(Xq,nXq)).
    generalize (Hopen q Xq) ; clear Hopen ; apply hinhfun ; intros (q0,(Xq0,Hq0)).
    right.
    exists q0 ; repeat split.
    + apply istrans_le_lt_ltNonnegativeRationals with (2 := Hq0).
      now apply isnonnegative_NonnegativeRationals.
    + exact Xq0.
    + intro H ; apply nXq.
      apply Hbot with (1 := H).
      now apply plusNonnegativeRationals_lecompat_r ; apply lt_leNonnegativeRationals.
Qed.
Lemma Dcuts_def_error'_correct2 (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) :
  Dcuts_def_bot X -> (0 < k)%NRat ->
  Dcuts_def_error' X k -> Dcuts_def_error X.
Proof.
  intros X k Hbot Hk0 H r Hr0.
  destruct (isdecrel_leNonnegativeRationals r k) as [Hrk | Hrk].
  - generalize (H r Hr0 Hrk) ; clear H ; apply hinhuniv ; intros [H | H].
    + apply hinhpr ; now left.
    + destruct H as (q,(_,Hq)).
      apply hinhpr ; right.
      exists q ; exact Hq.
  - apply notge_ltNonnegativeRationals in Hrk.
    generalize (H _ Hk0 (isrefl_leNonnegativeRationals k)) ; clear H ; apply hinhfun ; intros [H | H].
    + left.
      intros H0 ; apply H.
      apply Hbot with (1 := H0).
      now apply lt_leNonnegativeRationals.
    + right.
      destruct H as (q,(_,(Xq,nXq))).
      exists q ; split.
      * exact Xq.
      * intro H ; apply nXq.
        apply Hbot with (1 := H).
        now apply plusNonnegativeRationals_lecompat_l ; apply lt_leNonnegativeRationals.
Qed.

Lemma Dcuts_def_error_finite (X : hsubtypes NonnegativeRationals) :
  Dcuts_def_error X -> Dcuts_def_finite X.
Proof.
  intros X Hx.
  specialize (Hx _ ispositive_oneNonnegativeRationals).
  revert Hx ; apply hinhuniv ; intros [Hx|Hx].
  - apply hinhpr.
    exists 1 ; exact Hx.
  - destruct Hx as (x,(_,Hx)).
    apply hinhpr ; exists (x + 1) ; exact Hx.
Qed.

Lemma Dcuts_def_error_not_empty (X : hsubtypes NonnegativeRationals) :
  X 0 -> Dcuts_def_error X ->
  Π c : NonnegativeRationals,
    (0 < c)%NRat -> ∃ x : NonnegativeRationals, X x × ¬ X (x + c).
Proof.
  intros X X0 Hx c Hc.
  generalize (Hx c Hc).
  apply hinhuniv ; intros [ nXc | Hx' ].
  - apply hinhpr ; exists 0%NRat ; split.
    exact X0.
    rewrite islunit_zeroNonnegativeRationals.
    exact nXc.
  - apply hinhpr ; exact Hx'.
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
  Π X : Dcuts_set, Π r : NonnegativeRationals,
    neg (r ∈ X) -> Π n : NonnegativeRationals, n ∈ X -> n < r.
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

Definition Dcuts_le_rel : hrel Dcuts_set :=
  λ X Y : Dcuts_set,
          hProppair (Π x : NonnegativeRationals, x ∈ X -> x ∈ Y)
                    (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).

Lemma istrans_Dcuts_le_rel : istrans Dcuts_le_rel.
Proof.
  intros x y z Hxy Hyz r Xr.
  now apply Hyz, Hxy.
Qed.
Lemma isrefl_Dcuts_le_rel : isrefl Dcuts_le_rel.
Proof.
  now intros X x Xx.
Qed.

Lemma ispreorder_Dcuts_le_rel : ispreorder Dcuts_le_rel.
Proof.
  split.
  exact istrans_Dcuts_le_rel.
  exact isrefl_Dcuts_le_rel.
Qed.

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
  assert (Hr0 : 0%NRat < r' - r) by (now apply ispositive_minusNonnegativeRationals).
  generalize (is_Dcuts_error y _ Hr0) ; apply hinhuniv ; intros [Yq | Yq].
  - apply Utilities.squash_element ;
    right ; apply Utilities.squash_element.
    exists r' ; split.
    + intro H0 ; apply Yq.
      apply is_Dcuts_bot with r'.
      exact H0.
      now apply minusNonnegativeRationals_le.
    + exact Zr'.
  - destruct Yq as (q,(Yq,nYq)).
    destruct (isdecrel_leNonnegativeRationals (q + (r' - r)) r') as [Hdec | Hdec].
    + apply hinhpr ; right ; apply hinhpr.
      exists r' ; split.
      intro Yr' ; apply nYq.
      apply is_Dcuts_bot with r'.
      exact Yr'.
      exact Hdec.
      exact Zr'.
    + apply hinhpr ; left ; apply hinhpr.
      exists q ; split.
      * intro Xq ; apply Xr.
        apply is_Dcuts_bot with q.
        exact Xq.
        apply notge_ltNonnegativeRationals in Hdec.
        apply (plusNonnegativeRationals_ltcompat_r r) in Hdec ;
          rewrite isassoc_plusNonnegativeRationals, minusNonnegativeRationals_plus_r, iscomm_plusNonnegativeRationals in Hdec.
        apply_pr2_in plusNonnegativeRationals_ltcompat_r Hdec.
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

(** Effectively Ordered Set *)

Lemma Dcuts_lt_le_rel :
  Π x y : Dcuts_set, Dcuts_lt_rel x y -> Dcuts_le_rel x y.
Proof.
  intros x y ; apply hinhuniv ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply lt_leNonnegativeRationals.
  now apply Dcuts_finite with x.
Qed.

Lemma Dcuts_le_ngt_rel :
  Π x y : Dcuts_set, ¬ Dcuts_lt_rel x y <-> Dcuts_le_rel y x.
Proof.
  intros X Y.
  split.
  - intros Hnlt y Yy.
    generalize (is_Dcuts_open _ _ Yy) ; apply hinhuniv ; intros (y',(Yy',Hy)).
    apply ispositive_minusNonnegativeRationals in Hy.
    generalize (is_Dcuts_error X _ Hy) ; apply hinhuniv ; intros [nXc | ].
    + apply fromempty, Hnlt.
      apply hinhpr.
      exists y' ; split.
      * intro Xy' ; apply nXc.
        apply is_Dcuts_bot with (1 := Xy').
        now apply minusNonnegativeRationals_le.
      * exact Yy'.
    + intros (x,(Xx,Hx)).
      apply is_Dcuts_bot with (1 := Xx).
      apply notlt_geNonnegativeRationals ; intro H ; apply Hnlt.
      apply hinhpr.
      exists (x + (y' - y)) ; split.
      * exact Hx.
      * apply is_Dcuts_bot with (1 := Yy').
        pattern y' at 2 ; rewrite <- (minusNonnegativeRationals_plus_r y y').
        rewrite iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals, H.
        apply lt_leNonnegativeRationals ; apply_pr2 ispositive_minusNonnegativeRationals.
        exact Hy.
  - intros Hxy ; unfold neg.
    apply (hinhuniv (P := hProppair _ isapropempty)) ;
    intros (r,(Yr,Xr)).
    now apply Yr, Hxy.
Qed.

Lemma istrans_Dcuts_lt_le_rel :
  Π x y z : Dcuts_set, Dcuts_lt_rel x y -> Dcuts_le_rel y z -> Dcuts_lt_rel x z.
Proof.
  intros x y z Hlt Hle.
  revert Hlt ; apply hinhfun ; intros (r,(nXr,Yr)).
  exists r ; split.
  - exact nXr.
  - now apply Hle.
Qed.
Lemma istrans_Dcuts_le_lt_rel :
  Π x y z : Dcuts_set, Dcuts_le_rel x y -> Dcuts_lt_rel y z -> Dcuts_lt_rel x z.
Proof.
  intros x y z Hle.
  apply hinhfun ; intros (r,(nYr,Zr)).
  exists r ; split.
  - intros Xr ; apply nYr.
    now apply Hle.
  - exact Zr.
Qed.

Lemma iseo_Dcuts_le_lt_rel :
  isEffectiveOrder Dcuts_le_rel Dcuts_lt_rel.
Proof.
  split.
  - split.
    + exact ispreorder_Dcuts_le_rel.
    + exact isstpo_Dcuts_lt_rel.
  - repeat split.
    + now apply Dcuts_le_ngt_rel.
    + apply (pr2 (Dcuts_le_ngt_rel _ _)).
    + exact istrans_Dcuts_lt_le_rel.
    + exact istrans_Dcuts_le_lt_rel.
Qed.

Definition iseo_Dcuts : EffectiveOrder Dcuts_set :=
  pairEffectiveOrder Dcuts_le_rel Dcuts_lt_rel iseo_Dcuts_le_lt_rel.

Definition eo_Dcuts : EffectivelyOrderedSet :=
  pairEffectivelyOrderedSet iseo_Dcuts.

Definition Dcuts_le : po Dcuts_set := @EOle eo_Dcuts.
Definition Dcuts_ge : po Dcuts_set := @EOge eo_Dcuts.
Definition Dcuts_lt : StrongOrder Dcuts_set := @EOlt eo_Dcuts.
Definition Dcuts_gt : StrongOrder Dcuts_set := @EOgt eo_Dcuts.

Notation "x <= y" := (@EOle_rel eo_Dcuts x y) : Dcuts_scope.
Notation "x >= y" := (@EOge_rel eo_Dcuts x y) : Dcuts_scope.
Notation "x < y" := (@EOlt_rel eo_Dcuts x y) : Dcuts_scope.
Notation "x > y" := (@EOgt_rel eo_Dcuts x y) : Dcuts_scope.

(** ** Equivalence on [Dcuts] *)

Definition Dcuts_eq_rel :=
  λ X Y : Dcuts_set, Π r : NonnegativeRationals, (r ∈ X -> r ∈ Y) × (r ∈ Y -> r ∈ X).
Lemma isaprop_Dcuts_eq_rel : Π X Y : Dcuts_set, isaprop (Dcuts_eq_rel X Y).
Proof.
  intros X Y.
  apply impred_isaprop ; intro r.
  apply isapropdirprod.
  - now apply isapropimpl, pr2.
  - now apply isapropimpl, pr2.
Qed.
Definition Dcuts_eq : hrel Dcuts_set :=
  λ X Y : Dcuts_set, hProppair (Π r, dirprod (r ∈ X -> r ∈ Y) (r ∈ Y -> r ∈ X)) (isaprop_Dcuts_eq_rel X Y).

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
  Π x y : Dcuts_set,
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

(** ** Apartness on [Dcuts] *)

Lemma isaprop_Dcuts_ap_rel (X Y : Dcuts_set) :
  isaprop ((X < Y) ⨿ (Y < X)).
Proof.
  intros X Y.
  apply (isapropcoprod (X < Y) (Y < X)
                       (propproperty (X < Y))
                       (propproperty (Y < X))
                       (λ Hlt : X < Y, pr2 (Dcuts_le_ngt_rel Y X) (Dcuts_lt_le_rel X Y Hlt))).
Qed.
Definition Dcuts_ap_rel (X Y : Dcuts_set) : hProp :=
  hProppair ((X < Y) ⨿ (Y < X)) (isaprop_Dcuts_ap_rel X Y).

Lemma isirrefl_Dcuts_ap_rel : isirrefl Dcuts_ap_rel.
Proof.
  intros x.
  intros [Hap|Hap].
  now apply isirrefl_Dcuts_lt_rel with (1 := Hap).
  now apply isirrefl_Dcuts_lt_rel with (1 := Hap).
Qed.
Lemma issymm_Dcuts_ap_rel : issymm Dcuts_ap_rel.
Proof.
  intros x y.
  apply coprodcomm.
Qed.
Lemma iscotrans_Dcuts_ap_rel : iscotrans Dcuts_ap_rel.
Proof.
  intros x y z.
  intros [Hap|Hap].
  - generalize (iscotrans_Dcuts_lt_rel _ y _ Hap) ; apply hinhfun.
    intros [Hy | Hy].
    + now left ; left.
    + now right ; left.
  - generalize (iscotrans_Dcuts_lt_rel _ y _ Hap) ; apply hinhfun.
    intros [Hy | Hy].
    + now right ; right.
    + now left ; right.
Qed.

Lemma istight_Dcuts_ap_rel : istight Dcuts_ap_rel.
Proof.
  intros X Y Hap.
  apply Dcuts_eq_is_eq.
  intros r ; split ; revert r.
  - change (X <= Y).
    apply Dcuts_le_ngt_rel.
    intro Hlt ; apply Hap.
    now right.
  - change (Y <= X).
    apply Dcuts_le_ngt_rel.
    intro Hlt ; apply Hap.
    now left.
Qed.

Definition Dcuts : tightapSet :=
  Dcuts_set ,, Dcuts_ap_rel ,,
    (isirrefl_Dcuts_ap_rel ,, issymm_Dcuts_ap_rel ,, iscotrans_Dcuts_ap_rel) ,,
    istight_Dcuts_ap_rel.

Lemma not_Dcuts_ap_eq :
  Π x y : Dcuts, ¬ (x ≠ y) -> (x = y).
Proof.
  intros x y.
  now apply istight_Dcuts_ap_rel.
Qed.

(** *** Various theorems about order *)

Lemma Dcuts_ge_le :
  Π x y : Dcuts, x >= y -> y <= x.
Proof.
  easy.
Qed.
Lemma Dcuts_le_ge :
  Π x y : Dcuts, x <= y -> y >= x.
Proof.
  easy.
Qed.
Lemma Dcuts_eq_le :
  Π x y : Dcuts, Dcuts_eq x y -> x <= y.
Proof.
  intros x y Heq.
  intro r ;
    now apply (pr1 (Heq _)).
Qed.
Lemma Dcuts_eq_ge :
  Π x y : Dcuts, Dcuts_eq x y -> x >= y.
Proof.
  intros x y Heq.
  apply Dcuts_eq_le.
  now apply issymm_Dcuts_eq.
Qed.
Lemma Dcuts_le_ge_eq :
  Π x y : Dcuts, x <= y -> x >= y -> x = y.
Proof.
  intros x y le_xy ge_xy.
  apply Dcuts_eq_is_eq.
  split.
  now apply le_xy.
  now apply ge_xy.
Qed.

Lemma Dcuts_gt_lt :
  Π x y : Dcuts, (x > y) <-> (y < x).
Proof.
  now split.
Qed.
Lemma Dcuts_gt_ge :
  Π x y : Dcuts, x > y -> x >= y.
Proof.
  intros x y.
  now apply Dcuts_lt_le_rel.
Qed.

Lemma Dcuts_gt_nle :
  Π x y : Dcuts, x > y -> neg (x <= y).
Proof.
  intros x y Hlt Hle.
  now apply (pr2 (Dcuts_le_ngt_rel _ _)) in Hle.
Qed.
Lemma Dcuts_nlt_ge :
  Π x y : Dcuts, neg (x < y) <-> (x >= y).
Proof.
  intros X Y.
  now apply Dcuts_le_ngt_rel.
Qed.
Lemma Dcuts_lt_nge :
  Π x y : Dcuts, x < y -> neg (x >= y).
Proof.
  intros x y.
  now apply Dcuts_gt_nle.
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
    assert (Hn0 : (0 < q - r)%NRat) by (now apply ispositive_minusNonnegativeRationals).
    exists (q - r).
    split.
    + apply_pr2 (plusNonnegativeRationals_ltcompat_r r).
      rewrite minusNonnegativeRationals_plus_r.
      pattern q at 1 ;
        rewrite <- isrunit_zeroNonnegativeRationals.
      apply plusNonnegativeRationals_ltcompat_l.
      exact Hr0.
      now apply lt_leNonnegativeRationals, Hqr.
    + rewrite minusNonnegativeRationals_plus_r.
      now apply isirrefl_ltNonnegativeRationals.
      now apply lt_leNonnegativeRationals, Hqr.
  - now left.
Qed.

Definition NonnegativeRationals_to_Dcuts (q : NonnegativeRationals) : Dcuts :=
  mk_Dcuts (fun r => (r < q)%NRat)
           (NonnegativeRationals_to_Dcuts_bot q)
           (NonnegativeRationals_to_Dcuts_open q)
           (NonnegativeRationals_to_Dcuts_error q).


Lemma isapfun_NonnegativeRationals_to_Dcuts_aux :
  Π q q' : NonnegativeRationals,
    NonnegativeRationals_to_Dcuts q < NonnegativeRationals_to_Dcuts q'
    <-> (q < q')%NRat.
Proof.
  intros q q'.
  split.
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
  Π q q' : NonnegativeRationals,
    NonnegativeRationals_to_Dcuts q ≠ NonnegativeRationals_to_Dcuts q'
    -> q != q'.
Proof.
  intros q q'.
  intros [Hap | Hap].
  now apply ltNonnegativeRationals_noteq, isapfun_NonnegativeRationals_to_Dcuts_aux.
  now apply gtNonnegativeRationals_noteq, isapfun_NonnegativeRationals_to_Dcuts_aux.
Qed.
Lemma isapfun_NonnegativeRationals_to_Dcuts' :
  Π q q' : NonnegativeRationals,
    q != q'
    -> NonnegativeRationals_to_Dcuts q ≠ NonnegativeRationals_to_Dcuts q'.
Proof.
  intros q q' H.
  apply noteq_ltorgtNonnegativeRationals in H.
  destruct H.
  now left ; apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)).
  now right ; apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)).
Qed.

Definition Dcuts_zero : Dcuts := NonnegativeRationals_to_Dcuts 0%NRat.
Definition Dcuts_one : Dcuts := NonnegativeRationals_to_Dcuts 1%NRat.
Definition Dcuts_two : Dcuts := NonnegativeRationals_to_Dcuts 2.

Notation "0" := Dcuts_zero : Dcuts_scope.
Notation "1" := Dcuts_one : Dcuts_scope.
Notation "2" := Dcuts_two : Dcuts_scope.

(** Various usefull theorems *)

Lemma Dcuts_zero_empty :
  Π r : NonnegativeRationals, neg (r ∈ 0).
Proof.
  intros r ; simpl.
  change (neg (r < 0)%NRat).
  now apply isnonnegative_NonnegativeRationals'.
Qed.
Lemma Dcuts_notempty_notzero :
  Π (x : Dcuts) (r : NonnegativeRationals), r ∈ x -> x ≠ 0.
Proof.
  intros x r Hx.
  right.
  apply hinhpr.
  exists r.
  split.
  now apply Dcuts_zero_empty.
  exact Hx.
Qed.

Lemma Dcuts_ge_0 :
  Π x : Dcuts, Dcuts_zero <= x.
Proof.
  intros x r Hr.
  apply fromempty.
  revert Hr.
  now apply Dcuts_zero_empty.
Qed.
Lemma Dcuts_notlt_0 :
  Π x : Dcuts, ¬ (x < Dcuts_zero).
Proof.
  intros x.
  unfold neg.
  apply hinhuniv'.
  exact isapropempty.
  intros (r,(_)).
  now apply Dcuts_zero_empty.
Qed.

Lemma Dcuts_apzero_notempty :
  Π (x : Dcuts), (0%NRat ∈ x) <-> x ≠ 0.
Proof.
  intros x ; split.
  - now apply Dcuts_notempty_notzero.
  - intros [ | ].
    + apply hinhuniv ; intros (r,(_,Or)).
      now apply Dcuts_zero_empty in Or.
    + apply hinhuniv ; intros (r,(_,Xr)).
      apply is_Dcuts_bot with (1 := Xr).
      now apply isnonnegative_NonnegativeRationals.
Qed.

Lemma NonnegativeRationals_to_Dcuts_notin_le :
  Π (x : Dcuts) (r : NonnegativeRationals),
    ¬ (r ∈ x) -> x <= NonnegativeRationals_to_Dcuts r.
Proof.
  intros x r Hr q Hq.
  simpl.
  now apply (Dcuts_finite x).
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
      apply NonnegativeRationals_eq0_le0 in Hn.
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
        now apply NonnegativeRationals_neq0_gt0.
      * apply X_bot with (1 := Hrx).
        apply multNonnegativeRationals_le1_r.
        now apply divNonnegativeRationals_le1.
      * apply Y_bot with (1 := Hry).
        apply multNonnegativeRationals_le1_r.
        now apply divNonnegativeRationals_le1.
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
      now apply plusNonnegativeRationals_ltcompat.
Qed.
Lemma Dcuts_plus_error : Dcuts_def_error Dcuts_plus_val.
Proof.
  intros c Hc.
  apply ispositive_NQhalf in Hc.
  generalize (X_error _ Hc) (Y_error _ Hc).
  apply hinhfun2 ; intros [Hx [Hy | Hy ] | Hx [Hy | Hy] ].
  - left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
    + apply hinhuniv ; intros [Hz | Hz].
      * apply Hx.
        apply X_bot with (1 := Hz).
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
      * apply Hy.
        apply Y_bot with (1 := Hz).
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
    + apply hinhuniv ; intros ((rx,ry),(Hz,(Xr,Yr))).
      simpl in Hz,Xr,Yr.
      destruct (isdecrel_ltNonnegativeRationals rx (c / 2)%NRat) as [Hx' | Hx'].
      destruct (isdecrel_ltNonnegativeRationals ry (c / 2)%NRat) as [Hy' | Hy'].
      * apply (isirrefl_StrongOrder ltNonnegativeRationals c).
        pattern c at 1 ; rewrite Hz.
        rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_ltcompat.
        exact Hx'.
        exact Hy'.
      * apply Hy.
        apply Y_bot with (1 := Yr).
        now apply notlt_geNonnegativeRationals ; apply Hy'.
      * apply Hx.
        apply X_bot with (1 := Xr).
        now apply notlt_geNonnegativeRationals ; apply Hx'.
  - right.
    destruct Hy as (q,(Yq,nYq)).
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
      apply plusNonnegativeRationals_le_l.
    + apply nYq ; apply Y_bot with (1 := Yq').
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply plusNonnegativeRationals_le_r.
    + apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
      simpl in Hr,Xr,Yr.
      apply (isirrefl_StrongOrder ltNonnegativeRationals (q + c)).
      pattern (q + c) at 1 ; rewrite Hr.
      rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      rewrite iscomm_plusNonnegativeRationals.
      apply plusNonnegativeRationals_ltcompat.
      apply notge_ltNonnegativeRationals ; intro H.
      apply nYq ; apply Y_bot with (1 := Yr).
      exact H.
      apply notge_ltNonnegativeRationals ; intro H.
      apply Hx ; apply X_bot with (1 := Xr).
      exact H.
  - right.
    destruct Hx as (q,(Xq,nXq)).
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
      apply plusNonnegativeRationals_le_r.
    + apply Hy ; apply Y_bot with (1 := Yq).
      pattern c at 2 ; rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply plusNonnegativeRationals_le_l.
    + apply hinhuniv ; intros ((rx,ry),(Hr,(Xr,Yr))).
      simpl in Hr,Xr,Yr.
      apply (isirrefl_StrongOrder ltNonnegativeRationals (q + c)).
      pattern (q + c) at 1 ; rewrite Hr.
      rewrite (NQhalf_double c).
      rewrite <- isassoc_plusNonnegativeRationals.
      apply plusNonnegativeRationals_ltcompat.
      apply notge_ltNonnegativeRationals ; intro H.
      apply nXq ; apply X_bot with (1 := Xr).
      exact H.
      apply notge_ltNonnegativeRationals ; intro H.
      apply Hy ; apply Y_bot with (1 := Yr).
      exact H.
  - right.
    destruct Hx as (qx,(Xq,nXq)) ;
      destruct Hy as  (qy,(Yq,nYq)).
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
        apply plusNonnegativeRationals_le_r.
      * apply nYq, Y_bot with (1 := Yq').
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        rewrite (isassoc_plusNonnegativeRationals qx qy (c / 2)%NRat).
        rewrite (iscomm_plusNonnegativeRationals _ (qy + _)).
        rewrite (isassoc_plusNonnegativeRationals (qy + (c/2)%NRat)).
        apply plusNonnegativeRationals_le_r.
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
        apply plusNonnegativeRationals_ltcompat.
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
    apply NonnegativeRationals_eq0_le0 in Hn.
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
      now apply NonnegativeRationals_neq0_gt0.
    + apply Y_bot with (1 := Hry).
      apply multNonnegativeRationals_le1_r.
      now apply divNonnegativeRationals_le1.
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
    now apply multNonnegativeRationals_ltcompat_l.
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
  apply (pr2 (lt_gtNonnegativeRationals _ _)).
  apply (multNonnegativeRationals_ltcompat_l x ry y Hx).
  apply notge_ltNonnegativeRationals.
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
    apply (pr2 (lt_gtNonnegativeRationals _ _)).
    apply (multNonnegativeRationals_ltcompat_l x ry (c / x)%NRat Hx).
    apply notge_ltNonnegativeRationals.
    intro Hy' ; apply Hy.
    now apply Y_bot with ry.
    exact Hx.
  - right.
    destruct Hy as (q,(Yq,nYq)).
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
      apply (pr2 ( lt_gtNonnegativeRationals _ _)).
      apply (multNonnegativeRationals_ltcompat_l x ry (q + c / x)%NRat Hx).
      apply notge_ltNonnegativeRationals.
      intro Hy' ; apply nYq.
      now apply Y_bot with ry.
      exact Hx.
Qed.

End Dcuts_NQmult.

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
    apply NonnegativeRationals_eq0_le0 in Hn.
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
      now apply NonnegativeRationals_neq0_gt0.
    + exact Hrx.
    + apply Y_bot with (1 := Hry).
      apply multNonnegativeRationals_le1_r.
      now apply divNonnegativeRationals_le1.
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
    now apply multNonnegativeRationals_ltcompat.
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
    now apply multNonnegativeRationals_ltcompat.
  - apply Hy.
    apply Y_bot with (1 := Yr).
    now apply notlt_geNonnegativeRationals ; apply Hy'.
  - apply Hx.
    apply X_bot with (1 := Xr).
    now apply notlt_geNonnegativeRationals ; apply Hx'.
Qed.

Context (Hx1 : ¬ X 1%NRat).

Lemma Dcuts_mult_error_aux : Dcuts_def_error Dcuts_mult_val.
Proof.
  intros c Hc0.
  apply ispositive_NQhalf in Hc0.
  generalize (Y_error _ Hc0).
  apply hinhuniv ; intros [Hy | Hy].
  - apply hinhpr ; left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
    intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
    revert Hz.
    apply gtNonnegativeRationals_noteq.
    rewrite <- (islunit_oneNonnegativeRationals c).
    apply multNonnegativeRationals_ltcompat.
    apply notge_ltNonnegativeRationals ; intro H.
    now apply Hx1, X_bot with (1 := Xr).
    apply notge_ltNonnegativeRationals ; intro H.
    apply Hy, Y_bot with (1 := Yr).
    apply istrans_leNonnegativeRationals with (2 := H).
    pattern c at 2 ; rewrite (NQhalf_double c).
    now apply plusNonnegativeRationals_le_r.
  - destruct Hy as (y,(Yy,nYy)).
    assert (Hq1 : (0 < y + c / 2)%NRat).
    { apply istrans_lt_le_ltNonnegativeRationals with (c / 2)%NRat.
      exact Hc0.
      now apply plusNonnegativeRationals_le_l. }
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
      apply multNonnegativeRationals_ltcompat.
      apply notge_ltNonnegativeRationals ; intro H0.
      now apply nYy, Y_bot with (1 := Yr).
      apply notge_ltNonnegativeRationals ; intro H0.
      apply H, X_bot with (1 := Xr).
      exact H0.
      exact Hq1.
      rewrite <- (islunit_zeroNonnegativeRationals (c / 2)%NRat).
      pattern c at 2 ; rewrite (NQhalf_double c).
      now apply plusNonnegativeRationals_ltcompat_r.
    + right.
      destruct H as (x,(Xx,nXx)).
      exists (x * y) ; repeat split.
      * apply hinhpr.
        exists (x,y) ; simpl ; now repeat split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ;
        intros ((rx,ry),(Hz,(Xr,Yr))) ; simpl in Hz,Xr,Yr.
        revert Hz.
        apply gtNonnegativeRationals_noteq.
        apply istrans_lt_le_ltNonnegativeRationals with ((x + cx)* (y + (c / 2)%NRat)).
        apply multNonnegativeRationals_ltcompat.
        apply notge_ltNonnegativeRationals.
        now intros H ; apply nXx, X_bot with (1 := Xr).
        apply notge_ltNonnegativeRationals.
        now intros H ; apply nYy, Y_bot with (1 := Yr).
        rewrite isrdistr_mult_plusNonnegativeRationals, (iscomm_multNonnegativeRationals cx).
        unfold cx ; rewrite multdivNonnegativeRationals.
        pattern c at 3 ;
          rewrite (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_r.
        rewrite isldistr_mult_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        rewrite iscomm_multNonnegativeRationals.
        apply multNonnegativeRationals_le1_r.
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
  - destruct Hx as (x,(Xx,nXx)).
    assert (Hx1 : (0 < x + 1)%NRat).
    { apply istrans_lt_le_ltNonnegativeRationals with (1 := ispositive_oneNonnegativeRationals).
      apply plusNonnegativeRationals_le_l. }
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
      now apply ispositive_invNonnegativeRationals.
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
        hexists (λ l : NonnegativeRationals, (Π rx : NonnegativeRationals, X rx -> (r * rx <= l)%NRat)
                                               × (0 < l)%NRat × (l < 1)%NRat).

Lemma Dcuts_inv_in :
  Π x, (0 < x)%NRat -> X x -> (Dcuts_inv_val (/ x)%NRat) -> empty.
Proof.
  intros x Hx0 Xx.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (l,(H,(Hl0,Hl1))).
  specialize (H _ Xx).
  rewrite islinv_NonnegativeRationals in H.
  apply (pr2 (notlt_geNonnegativeRationals _ _)) in H.
  now apply H, Hl1.
  exact Hx0.
Qed.
Lemma Dcuts_inv_out :
  Π x, ¬ (X x) -> Π y, (x < y)%NRat -> Dcuts_inv_val (/ y)%NRat.
Proof.
  intros x nXx y Hy.
  apply hinhpr.
  exists (x / y)%NRat ; repeat split.
  - intros rx Hrx.
    unfold divNonnegativeRationals.
    rewrite iscomm_multNonnegativeRationals.
    apply multNonnegativeRationals_lecompat_r.
    apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
    intros H ; apply nXx.
    now apply X_bot with (1 := Hrx).
  - apply ispositive_divNonnegativeRationals.
    apply notge_ltNonnegativeRationals.
    intros H ; apply nXx.
    now apply X_bot with (1 := X_0).
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
  - apply_pr2 (multNonnegativeRationals_ltcompat_r y).
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
    unfold divNonnegativeRationals.
    rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals.
    exact Hy.
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
    now apply multNonnegativeRationals_lecompat_r.
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
        apply (multNonnegativeRationals_lecompat_l' (r * r)).
        now apply ispositive_multNonnegativeRationals.
        rewrite <- isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        rewrite isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (2 := NQmax_le_r _ _).
        apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals ; intro H ; apply Hr'.
        now apply X_bot with (1 := Xrx).
        exact Hr0.
        now apply ispositive_multNonnegativeRationals.
      * now apply ispositive_invNonnegativeRationals.
      * apply_pr2 (multNonnegativeRationals_ltcompat_l r).
        easy.
        now rewrite isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
    + apply ispositive_invNonnegativeRationals.
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
        apply multNonnegativeRationals_lecompat_r.
        now apply Hr.
        exact Hl0.
      * apply istrans_le_lt_ltNonnegativeRationals with (2 := Hl').
        now apply isnonnegative_NonnegativeRationals.
      * exact Hl'1.
    + pattern r at 1 ; rewrite <- (islunit_oneNonnegativeRationals r).
      apply multNonnegativeRationals_ltcompat_r.
      exact Hr0.
      apply_pr2 (multNonnegativeRationals_ltcompat_r l).
      exact Hl0.
      rewrite islunit_oneNonnegativeRationals.
      now rewrite iscomm_multNonnegativeRationals, multdivNonnegativeRationals.
Qed.

Context (X_1 : X 1%NRat).

Lemma Dcuts_inv_error_aux : Dcuts_def_error Dcuts_inv_val.
Proof.
  assert (Π c, (0 < c)%NRat -> hexists (λ q : NonnegativeRationals, X q × ¬ X (q + c))).
  { intros c Hc0.
    generalize (X_error c Hc0) ; apply hinhuniv ; intros [nXc | H].
    - apply hinhpr.
      exists 0%NRat ; split.
      + exact X_0.
      + now rewrite islunit_zeroNonnegativeRationals.
    - apply hinhpr ; exact H. }
  clear X_error ; rename X0 into X_error.

  intros c Hc0.
  apply ispositive_NQhalf in Hc0.
  specialize (X_error _ Hc0) ; revert X_error.
  apply hinhfun ; intros (r,(Xr,nXr)).
  right.
  exists (/ (NQmax 1%NRat r + c))%NRat ; split.
  - apply Dcuts_inv_out with (1 := nXr).
    pattern c at 2 ; rewrite (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
    eapply istrans_le_lt_ltNonnegativeRationals, plusNonnegativeRationals_lt_r.
    apply plusNonnegativeRationals_lecompat_r ; apply NQmax_le_r.
    exact Hc0.
  - assert (Xmax : X (NQmax 1%NRat r)) by (now apply NQmax_case).
    assert (Hmax : (0 < NQmax 1 r)%NRat).
    { eapply istrans_lt_le_ltNonnegativeRationals, NQmax_le_l.
      now eapply ispositive_oneNonnegativeRationals. }
    intro Hinv ; apply (Dcuts_inv_in _ Hmax Xmax), Dcuts_inv_bot with (1 := Hinv).
    apply lt_leNonnegativeRationals, minusNonnegativeRationals_ltcompat_l' with (/ (NQmax 1 r + c))%NRat.
    rewrite plusNonnegativeRationals_minus_l.
    rewrite minus_divNonnegativeRationals, plusNonnegativeRationals_minus_l.
    unfold divNonnegativeRationals ;
      apply_pr2 (multNonnegativeRationals_ltcompat_r (NQmax 1 r * (NQmax 1 r + c))%NRat).
    apply ispositive_multNonnegativeRationals.
    exact Hmax.
    now apply ispositive_plusNonnegativeRationals_l.
    rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals.
    apply multNonnegativeRationals_ltcompat_l.
    now apply_pr2 ispositive_NQhalf.
    pattern 1%NRat at 1 ;
      rewrite <- (islunit_oneNonnegativeRationals 1%NRat).
    apply istrans_le_lt_ltNonnegativeRationals with (NQmax 1 r * 1)%NRat.
    now apply multNonnegativeRationals_lecompat_r, NQmax_le_l.
    apply multNonnegativeRationals_ltcompat_l.
    exact Hmax.
    apply istrans_le_lt_ltNonnegativeRationals with (1 := NQmax_le_l _ r).
    apply plusNonnegativeRationals_lt_r.
    now apply_pr2 ispositive_NQhalf.
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
  now apply ispositive_invNonnegativeRationals.
  now apply Dcuts_inv_bot.
  apply Dcuts_inv_error_aux.
  now unfold Y ; apply Dcuts_NQmult_bot.
  unfold Y ; apply Dcuts_NQmult_error.
  now apply ispositive_invNonnegativeRationals.
  exact X_bot.
  exact X_error.
  apply hinhpr ; exists 0%NRat ; split.
  now rewrite israbsorb_zero_multNonnegativeRationals.
  exact X_0.
  exact Y_1.
Qed.

End Dcuts_inv'.

Definition Dcuts_inv (X : Dcuts) (X_0 : X ≠ 0) : Dcuts.
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
    now apply_pr2 Dcuts_apzero_notempty.
Defined.

(** ** Algebraic properties *)

Lemma Dcuts_NQmult_mult :
  Π (x : NonnegativeRationals) (y : Dcuts) (Hx0 : (0 < x)%NRat), Dcuts_NQmult x y Hx0 = Dcuts_mult (NonnegativeRationals_to_Dcuts x) y.
Proof.
  intros x y Hx0.
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv.
    intros ry.
    generalize (is_Dcuts_open _ _ (pr2 (pr2 ry))).
    apply hinhfun ; intros ry'.
    exists (((x * (pr1 ry)) / (pr1 ry'))%NRat, (pr1 ry')).
    simpl.
    assert (Hry' : (0 < pr1 ry')%NRat).
    { eapply istrans_le_lt_ltNonnegativeRationals, (pr2 (pr2 ry')).
      apply isnonnegative_NonnegativeRationals. }
    split ; [ | split].
    + unfold divNonnegativeRationals.
      rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
      exact (pr1 (pr2 ry)).
      exact Hry'.
    + pattern x at 4.
      rewrite <- (isrunit_oneNonnegativeRationals x).
      unfold divNonnegativeRationals.
      rewrite isassoc_multNonnegativeRationals.
      apply multNonnegativeRationals_ltcompat_l.
      exact Hx0.
      rewrite <- (isrinv_NonnegativeRationals (pr1 ry')).
      apply multNonnegativeRationals_ltcompat_r.
      apply ispositive_invNonnegativeRationals.
      exact Hry'.
      exact (pr2 (pr2 ry')).
      exact Hry'.
    + exact (pr1 (pr2 ry')).
  - apply hinhfun ; simpl.
    intros xy.
    exists (fst (pr1 xy) * snd (pr1 xy) / x).
    split.
    + rewrite iscomm_multNonnegativeRationals.
      unfold divNonnegativeRationals.
      rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
      exact (pr1 (pr2 xy)).
      exact Hx0.
    + apply is_Dcuts_bot with (1 := pr2 (pr2 (pr2 xy))).
      pattern (snd (pr1 xy)) at 2.
      rewrite <- (isrunit_oneNonnegativeRationals (snd (pr1 xy))), <- (isrinv_NonnegativeRationals x), <- isassoc_multNonnegativeRationals.
      apply multNonnegativeRationals_lecompat_r.
      rewrite iscomm_multNonnegativeRationals.
      apply multNonnegativeRationals_lecompat_l.
      apply lt_leNonnegativeRationals.
      exact (pr1 (pr2 (pr2 xy))).
      exact Hx0.
Qed.

Lemma iscomm_Dcuts_plus : iscomm Dcuts_plus.
Proof.
  assert (H : Π x y, Π x0 : NonnegativeRationals, x0 ∈ Dcuts_plus x y -> x0 ∈ Dcuts_plus y x).
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
  Π x x' y : Dcuts, Dcuts_plus x y < Dcuts_plus x' y -> x < x'.
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
  intros [Hlt | Hlt].
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
  Π x x' y : Dcuts, Dcuts_mult x y < Dcuts_mult x' y -> x < x'.
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
  intros [Hlt | Hlt].
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
      * now apply Dcuts_zero_empty in Hr.
      * exact Hr.
    + intros ((r0,rx),(_,(Hr,_))).
      now apply Dcuts_zero_empty in Hr.
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
    now apply multNonnegativeRationals_le1_r, lt_leNonnegativeRationals.
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
       apply_pr2 (multNonnegativeRationals_ltcompat_l q).
       apply istrans_le_lt_ltNonnegativeRationals with (2 := Hrq).
       apply isnonnegative_NonnegativeRationals.
       rewrite multdivNonnegativeRationals, isrunit_oneNonnegativeRationals.
       exact Hrq.
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
  Π x : Dcuts, Dcuts_mult Dcuts_zero x = Dcuts_zero.
Proof.
  intros x.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((ri,rx),(Hr,(Or,Xr))).
    now apply Dcuts_zero_empty in Or.
  - intro Hr.
    now apply Dcuts_zero_empty in Hr.
Qed.
Lemma israbsorb_Dcuts_mult_zero :
  Π x : Dcuts, Dcuts_mult x Dcuts_zero = Dcuts_zero.
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
      apply NonnegativeRationals_eq0_le0 in Heq.
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
        apply multNonnegativeRationals_le1_r, divNonnegativeRationals_le1.
        now apply NQmax_le_l.
        apply is_Dcuts_bot with (1 := Yr).
        rewrite Hzy, iscomm_multNonnegativeRationals.
        unfold divNonnegativeRationals ;
          rewrite isassoc_multNonnegativeRationals.
        apply multNonnegativeRationals_le1_r, divNonnegativeRationals_le1.
        now apply NQmax_le_r.
Qed.
Lemma isrdistr_Dcuts_plus_mult : isrdistr Dcuts_plus Dcuts_mult.
Proof.
  intros x y z.
  rewrite <- ! (iscomm_Dcuts_mult z).
  now apply isldistr_Dcuts_plus_mult.
Qed.

Lemma Dcuts_ap_one_zero : 1 ≠ 0.
Proof.
  apply isapfun_NonnegativeRationals_to_Dcuts'.
  apply gtNonnegativeRationals_noteq.
  exact ispositive_oneNonnegativeRationals.
Qed.
Definition islinv_Dcuts_inv :
  Π x : Dcuts, Π Hx0 : x ≠ 0, Dcuts_mult (Dcuts_inv x Hx0) x = 1.
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
    apply_pr2_in Dcuts_apzero_notempty Hx0.
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
        apply (pr1 (ispositive_invNonnegativeRationals _)).
        exact ispositive_twoNonnegativeRationals.
        apply_pr2 (multNonnegativeRationals_ltcompat_l 2%NRat).
        exact ispositive_twoNonnegativeRationals.
        rewrite isrunit_oneNonnegativeRationals, isrinv_NonnegativeRationals.
        exact one_lt_twoNonnegativeRationals.
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
        apply ispositive_minusNonnegativeRationals.
        apply_pr2 (multNonnegativeRationals_ltcompat_l t).
        now apply istrans_ltNonnegativeRationals with q.
        rewrite isrunit_oneNonnegativeRationals, isrinv_NonnegativeRationals.
        exact Ht1.
        now apply istrans_ltNonnegativeRationals with q. }
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
        apply multNonnegativeRationals_lecompat_l, lt_leNonnegativeRationals.
        apply (Dcuts_finite x).
        intro H ; apply nXr'.
        apply is_Dcuts_bot with (1 := H).
        now apply plusNonnegativeRationals_lecompat_r ; apply NQmax_le_r.
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
        apply_pr2 (multNonnegativeRationals_ltcompat_l (/ q)%NRat).
        now apply ispositive_invNonnegativeRationals.
        rewrite isrunit_oneNonnegativeRationals, <- !isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        2: exact Hq0.
        apply_pr2 (multNonnegativeRationals_ltcompat_l (NQmax r r')).
        apply istrans_lt_le_ltNonnegativeRationals with r.
        exact Hr0.
        now apply NQmax_le_l.
        rewrite <- !isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
        2: apply istrans_lt_le_ltNonnegativeRationals with r.
        2: exact Hr0.
        2: now apply NQmax_le_l.
        apply (minusNonnegativeRationals_ltcompat_l' _ _ (NQmax r r' * 1)%NRat).
        rewrite <- isldistr_mult_minusNonnegativeRationals, isrunit_oneNonnegativeRationals, plusNonnegativeRationals_minus_l.
        unfold c.
        apply multNonnegativeRationals_le_lt.
        exact Hr0.
        now apply NQmax_le_l.
        apply_pr2 (multNonnegativeRationals_ltcompat_l q).
        exact Hq0.
        rewrite !isldistr_mult_minusNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        2: exact Hq0.
        apply_pr2 (multNonnegativeRationals_ltcompat_r t).
        now apply istrans_ltNonnegativeRationals with q.
        rewrite !isrdistr_mult_minusNonnegativeRationals, isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals, islunit_oneNonnegativeRationals.
        2: now apply istrans_ltNonnegativeRationals with q.
        apply minusNonnegativeRationals_ltcompat_l.
        exact Ht.
        pattern t at 2 ;
          rewrite <- (islunit_oneNonnegativeRationals t).
        apply multNonnegativeRationals_ltcompat_r.
        now apply istrans_ltNonnegativeRationals with q.
        now apply istrans_ltNonnegativeRationals with t.
      * simpl.
        now apply NQmax_case.
Qed.
Lemma isrinv_Dcuts_inv :
  Π x : Dcuts, Π Hx0 : x ≠ 0, Dcuts_mult x (Dcuts_inv x Hx0) = 1.
Proof.
  intros x Hx0.
  rewrite iscomm_Dcuts_mult.
  now apply islinv_Dcuts_inv.
Qed.

Lemma Dcuts_plus_ltcompat_l :
  Π x y z: Dcuts, (y < z) <-> (Dcuts_plus y x < Dcuts_plus z x).
Proof.
  intros x y z.
  split.
  - apply hinhuniv ; intros (r,(nYr,Zr)).
    generalize (is_Dcuts_open _ _ Zr) ; apply hinhuniv ; intros (r',(Zr',Hr)).
    apply ispositive_minusNonnegativeRationals in Hr.
    generalize (is_Dcuts_error x _ Hr).
    apply hinhuniv ; intros [nXc | ].
    + apply hinhpr ; exists r' ; split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ] ; apply hinhuniv ; [intros [Yr' | Xr'] | intros ((ry,rx),(Hr',(Yr',Xr')))].
        apply nYr, is_Dcuts_bot with (1 := Yr'), lt_leNonnegativeRationals.
        now apply_pr2 ispositive_minusNonnegativeRationals.
        apply nXc, is_Dcuts_bot with (1 := Xr'), minusNonnegativeRationals_le.
        simpl in Hr',Yr',Xr'.
        revert Hr' ; apply gtNonnegativeRationals_noteq.
        rewrite <- (minusNonnegativeRationals_plus_r r r'), iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_ltcompat.
        now apply (Dcuts_finite y).
        now apply (Dcuts_finite x).
        apply lt_leNonnegativeRationals.
        now apply_pr2 ispositive_minusNonnegativeRationals.
      * apply hinhpr ; left.
        now apply hinhpr ; left.
    + intros (q,(Xq,nXq)).
      apply hinhpr.
      exists (r' + q)%NRat ; split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ] ; apply hinhuniv ; [intros [Yr' | Xr'] | intros ((ry,rx),(Hr',(Yr',Xr')))].
        apply nYr, is_Dcuts_bot with (1 := Yr'), lt_leNonnegativeRationals.
        rewrite <- (isrunit_zeroNonnegativeRationals r).
        apply plusNonnegativeRationals_lt_le_ltcompat.
        now apply_pr2 ispositive_minusNonnegativeRationals.
        now apply isnonnegative_NonnegativeRationals.
        apply nXq, is_Dcuts_bot with (1 := Xr').
        rewrite iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_r.
        now apply minusNonnegativeRationals_le.
        simpl in Hr',Yr',Xr'.
        revert Hr' ; apply gtNonnegativeRationals_noteq.
        rewrite iscomm_plusNonnegativeRationals, <- (minusNonnegativeRationals_plus_r r r'), <- isassoc_plusNonnegativeRationals, iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_ltcompat.
        now apply (Dcuts_finite y).
        now apply (Dcuts_finite x).
        apply lt_leNonnegativeRationals.
        now apply_pr2 ispositive_minusNonnegativeRationals.
      * apply hinhpr ; right.
        apply hinhpr ; exists (r',q) ; repeat split.
        exact Zr'.
        exact Xq.
  - now apply Dcuts_plus_lt_l.
Qed.
Lemma Dcuts_plus_lecompat_l :
  Π x y z: Dcuts, (y <= z) <-> (Dcuts_plus y x <= Dcuts_plus z x).
Proof.
  intros x y z.
  split.
  - intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
    now apply_pr2 (Dcuts_plus_ltcompat_l x).
  - intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
    now apply Dcuts_plus_ltcompat_l.
Qed.
Lemma Dcuts_plus_ltcompat_r :
  Π x y z: Dcuts, (y < z) <-> (Dcuts_plus x y < Dcuts_plus x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_plus x).
  now apply Dcuts_plus_ltcompat_l.
Qed.
Lemma Dcuts_plus_lecompat_r :
  Π x y z: Dcuts, (y <= z) <-> (Dcuts_plus x y <= Dcuts_plus x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_plus x).
  now apply Dcuts_plus_lecompat_l.
Qed.

Lemma Dcuts_plus_le_l :
  Π x y, x <= Dcuts_plus x y.
Proof.
  intros x y r Xr.
  apply hinhpr ; left.
  now apply hinhpr ; left.
Qed.
Lemma Dcuts_plus_le_r :
  Π x y, y <= Dcuts_plus x y.
Proof.
  intros x y r Xr.
  apply hinhpr ; left.
  now apply hinhpr ; right.
Qed.

Lemma Dcuts_mult_ltcompat_l :
  Π x y z: Dcuts, (0 < x) -> (y < z) -> (Dcuts_mult y x < Dcuts_mult z x).
Proof.
  intros X Y Z.
  apply hinhuniv2 ; intros (x,(_,Xx)) (r,(nYr,Zr)).
  generalize (is_Dcuts_bot _ _ Xx _ (isnonnegative_NonnegativeRationals _)) ; clear x Xx ; intro X0.
  case (eq0orgt0NonnegativeRationals r) ; intro Hr0.
  - rewrite Hr0 in nYr, Zr ; clear r Hr0.
    apply hinhpr ; exists 0%NRat ; split.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros ((ry,rx),(Hr,(Yr,Xr))).
      simpl in Hr,Yr,Xr.
      apply nYr.
      apply is_Dcuts_bot with (1 := Yr).
      now apply isnonnegative_NonnegativeRationals.
    + apply hinhpr ; exists (0%NRat,0%NRat) ; simpl ; repeat split.
      now rewrite islabsorb_zero_multNonnegativeRationals.
      exact Zr.
      exact X0.
  - generalize (is_Dcuts_open _ _ X0) ; apply hinhuniv ; intros (x,(Xx,Hx0)).
    generalize (is_Dcuts_open _ _ Zr) ; apply hinhuniv ; intros (r',(Zr',Hr)).
    set (c := ((r' - r) / r * x)%NRat).
    assert (Hc0 : (0 < c)%NRat).
    { unfold c.
      apply ispositive_multNonnegativeRationals.
      apply ispositive_divNonnegativeRationals.
      now apply ispositive_minusNonnegativeRationals.
      exact Hr0.
      exact Hx0. }
    generalize (Dcuts_def_error_not_empty _ X0 (is_Dcuts_error _) _ Hc0) ; apply hinhfun ; intros (x',(Xx',nXx')).
    exists (r * (NQmax x x' + c))%NRat ; split.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros ((ry,rx)); simpl ; intros (Hr',(Yr,Xr)).
      revert Hr' ; apply gtNonnegativeRationals_noteq.
      apply multNonnegativeRationals_ltcompat.
      now apply (Dcuts_finite Y).
      apply (Dcuts_finite X).
      intro ; apply nXx'.
      apply is_Dcuts_bot with (1 := X1).
      apply plusNonnegativeRationals_lecompat_r.
      now apply NQmax_le_r.
      exact Xr.
    + apply hinhpr ; exists (r',((r * (NQmax x x' + c)) / r')%NRat) ; simpl ; repeat split.
      * rewrite multdivNonnegativeRationals.
        reflexivity.
        now apply istrans_ltNonnegativeRationals with r.
      * exact Zr'.
      * apply (is_Dcuts_bot _ (NQmax x x')%NRat).
        now apply NQmax_case.
        apply multNonnegativeRationals_lecompat_r' with r'.
        now apply istrans_ltNonnegativeRationals with r.
        unfold divNonnegativeRationals.
        rewrite !isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, isrunit_oneNonnegativeRationals, isldistr_mult_plusNonnegativeRationals, iscomm_multNonnegativeRationals.
        apply (minusNonnegativeRationals_lecompat_l' (NQmax x x' * r)%NRat).
        now apply multNonnegativeRationals_lecompat_l, lt_leNonnegativeRationals.
        rewrite plusNonnegativeRationals_minus_l.
        rewrite <- isldistr_mult_minusNonnegativeRationals, iscomm_multNonnegativeRationals.
        apply multNonnegativeRationals_lecompat_r' with (/ r).
        now apply ispositive_invNonnegativeRationals.
        rewrite !isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals, iscomm_multNonnegativeRationals.
        apply multNonnegativeRationals_lecompat_l.
        now apply NQmax_le_l.
        exact Hr0.
        now apply istrans_ltNonnegativeRationals with r.
Qed.
Lemma Dcuts_mult_ltcompat_l' :
  Π x y z: Dcuts, (Dcuts_mult y x < Dcuts_mult z x) -> (y < z).
Proof.
  intros x y z.
  now apply Dcuts_mult_lt_l.
Qed.
Lemma Dcuts_mult_lecompat_l :
  Π x y z: Dcuts, (0 < x) -> (Dcuts_mult y x <= Dcuts_mult z x) -> (y <= z).
Proof.
  intros x y z Hx0.
  intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
  now apply Dcuts_mult_ltcompat_l.
Qed.
Lemma Dcuts_mult_lecompat_l' :
  Π x y z: Dcuts, (y <= z) -> (Dcuts_mult y x <= Dcuts_mult z x).
Proof.
  intros x y z.
  intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
  now apply (Dcuts_mult_ltcompat_l' x).
Qed.

Lemma Dcuts_mult_ltcompat_r :
  Π x y z: Dcuts, (0 < x) -> (y < z) -> (Dcuts_mult x y < Dcuts_mult x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_ltcompat_l.
Qed.
Lemma Dcuts_mult_ltcompat_r' :
  Π x y z: Dcuts, (Dcuts_mult x y < Dcuts_mult x z) -> (y < z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_ltcompat_l'.
Qed.
Lemma Dcuts_mult_lecompat_r :
  Π x y z: Dcuts, (0 < x) -> (Dcuts_mult x y <= Dcuts_mult x z) -> (y <= z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_lecompat_l.
Qed.
Lemma Dcuts_mult_lecompat_r' :
  Π x y z: Dcuts, (y <= z) -> (Dcuts_mult x y <= Dcuts_mult x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_lecompat_l'.
Qed.

Lemma Dcuts_plus_double :
  Π x : Dcuts, Dcuts_plus x x = Dcuts_mult Dcuts_two x.
Proof.
  intros x.
  rewrite <- (Dcuts_NQmult_mult _ _ ispositive_twoNonnegativeRationals).
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv ; intros [ | ] ; apply hinhfun ; [intros [Xr | Xr] | intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr))].
    + exists (r / 2)%NRat.
      simpl ; split.
      * apply pathsinv0, multdivNonnegativeRationals.
        exact ispositive_twoNonnegativeRationals.
      * apply is_Dcuts_bot with (1 := Xr).
        pattern r at 2 ; rewrite (NQhalf_double r).
        apply plusNonnegativeRationals_le_l.
    + exists (r / 2)%NRat.
      simpl ; split.
      * apply pathsinv0, multdivNonnegativeRationals.
        exact ispositive_twoNonnegativeRationals.
      * apply is_Dcuts_bot with (1 := Xr).
        pattern r at 2 ; rewrite (NQhalf_double r).
        apply plusNonnegativeRationals_le_l.
    + exists ((rx + ry) / 2)%NRat.
      split.
      * apply pathsinv0, multdivNonnegativeRationals.
        exact ispositive_twoNonnegativeRationals.
      * destruct (isdecrel_ltNonnegativeRationals rx ry).
        apply is_Dcuts_bot with (1 := Yr).
        pattern ry at 2 ; rewrite (NQhalf_double ry).
        unfold divNonnegativeRationals.
        rewrite isrdistr_mult_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_r.
        apply multNonnegativeRationals_lecompat_r.
        now apply lt_leNonnegativeRationals.
        apply is_Dcuts_bot with (1 := Xr).
        pattern rx at 2 ; rewrite (NQhalf_double rx).
        unfold divNonnegativeRationals.
        rewrite isrdistr_mult_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        apply multNonnegativeRationals_lecompat_r.
        now apply notlt_geNonnegativeRationals.
  - apply hinhfun ; intros (q,(->,Xq)).
    right.
    apply hinhpr.
    exists (q,q).
    repeat split.
    + assert (2 = 1+1)%NRat.
      { apply subtypeEquality_prop ; simpl.
        apply hq2eq1plus1. }
      rewrite X ; clear X.
      rewrite isrdistr_mult_plusNonnegativeRationals, islunit_oneNonnegativeRationals.
      reflexivity.
    + exact Xq.
    + exact Xq.
Qed.

(** ** Structures *)

Definition Dcuts_setwith2binop : setwith2binop.
Proof.
  exists Dcuts.
  split.
  - exact Dcuts_plus.
  - exact Dcuts_mult.
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

Definition Dcuts_commrig : commrig.
Proof.
  exists Dcuts_setwith2binop.
  repeat split.
  - exists (isabmonoidop_Dcuts_plus,,ismonoidop_Dcuts_mult).
    split.
    + exact islabsorb_Dcuts_mult_zero.
    + exact israbsorb_Dcuts_mult_zero.
  - exact isldistr_Dcuts_plus_mult.
  - exact isrdistr_Dcuts_plus_mult.
  - exact iscomm_Dcuts_mult.
Defined.

Definition Dcuts_ConstructiveCommutativeDivisionRig : ConstructiveCommutativeDivisionRig.
Proof.
  exists Dcuts_commrig.
  exists (pr2 Dcuts).
  repeat split.
  - exact islapbinop_Dcuts_plus.
  - exact israpbinop_Dcuts_plus.
  - exact islapbinop_Dcuts_mult.
  - exact israpbinop_Dcuts_mult.
  - exact Dcuts_ap_one_zero.
  - intros x Hx.
    exists (Dcuts_inv x Hx) ; split.
    + exact (islinv_Dcuts_inv x Hx).
    + exact (isrinv_Dcuts_inv x Hx).
Defined.

(** ** Additional usefull definitions *)
(** *** Dcuts_minus *)

Section Dcuts_minus.

  Context (X : hsubtypes NonnegativeRationals).
  Context (X_bot : Dcuts_def_bot X).
  Context (X_open : Dcuts_def_open X).
  Context (X_error : Dcuts_def_error X).
  Context (Y : hsubtypes NonnegativeRationals).
  Context (Y_bot : Dcuts_def_bot Y).
  Context (Y_open : Dcuts_def_open Y).
  Context (Y_error : Dcuts_def_error Y).

Definition Dcuts_minus_val : hsubtypes NonnegativeRationals :=
  fun r => hexists (λ x, X x × Π y, (Y y) ⨿ (y = 0%NRat) -> (r < x - y)%NRat).

Lemma Dcuts_minus_bot : Dcuts_def_bot Dcuts_minus_val.
Proof.
  intros r Hr q Hle.
  revert Hr ; apply hinhfun ; intros (x,(Xx,Hx)).
  exists x ; split.
  - exact Xx.
  - intros y Yy.
    apply istrans_le_lt_ltNonnegativeRationals with r.
    exact Hle.
    now apply Hx.
Qed.

Lemma Dcuts_minus_open : Dcuts_def_open Dcuts_minus_val.
Proof.
  intros r.
  apply hinhuniv ; intros (x,(Xx,Hx)).
  generalize (X_open x Xx).
  apply hinhfun ; intros (x',(Xx',Hx')).
  exists (r + (x' - x)) ; split.
  - apply hinhpr ; exists x' ; split.
    + exact Xx'.
    + intros y Yy.
      case (isdecrel_leNonnegativeRationals y x) ; intro Hxy.
      * apply istrans_lt_le_ltNonnegativeRationals with ((x - y) + (x' - x)).
        apply plusNonnegativeRationals_ltcompat_r.
        now apply Hx.
        rewrite minusNonnegativeRationals_plus_exchange.
        rewrite iscomm_plusNonnegativeRationals, minusNonnegativeRationals_plus_r.
        now apply isrefl_leNonnegativeRationals.
        now apply lt_leNonnegativeRationals.
        exact Hxy.
      * apply notge_ltNonnegativeRationals in Hxy.
        apply fromempty.
        generalize (Hx y Yy).
        rewrite minusNonnegativeRationals_eq_zero.
        now apply isnonnegative_NonnegativeRationals'.
        now apply lt_leNonnegativeRationals.
  - apply plusNonnegativeRationals_lt_r.
    now apply ispositive_minusNonnegativeRationals.
Qed.

Lemma Dcuts_minus_error : Dcuts_def_error Dcuts_minus_val.
Proof.
  assert (Y_error' : Dcuts_def_error (λ y, Y y ∨ (y = 0%NRat))).
  { intros c Hc.
    generalize (Y_error c Hc) ; apply hinhfun ; intros [Yc | Hy ].
    - left.
      intros H ; apply Yc ; clear Yc ; revert H.
      apply hinhuniv ; intros [Yc | Hc0].
      + exact Yc.
      + rewrite Hc0 in Hc.
        now apply fromempty, (isirrefl_ltNonnegativeRationals 0%NRat).
    - right ; destruct Hy as (y,(Yy,nYy)).
      exists y ; split.
      + now apply hinhpr ; left.
      + intros H ; apply nYy ; revert H.
        apply hinhuniv ; intros [H | Hc0].
        * exact H.
        * apply fromempty ; revert Hc0.
          apply gtNonnegativeRationals_noteq.
          now apply ispositive_plusNonnegativeRationals_r. }
  intros c Hc.
  apply ispositive_NQhalf in Hc.
  apply (fun X X0 Xerr => Dcuts_def_error_not_empty X X0 Xerr _ Hc) in Y_error'.
  revert Y_error' ; apply hinhuniv ; intros (y,(Yy,nYy)).
  revert Yy ; apply hinhuniv ; intros Yy.
  assert (¬ Y (y + c / 2%NRat)).
  { intro ; apply nYy.
    now apply hinhpr ; left. }
  clear nYy ; rename X0 into nYy.
  generalize (X_error _ Hc) ; apply hinhuniv ; intros [Xc | Hx].

  - apply hinhpr ; left ; intro H ; apply Xc.
    revert H ; apply hinhuniv ; intros (x,(Xx,Hx)).
    apply X_bot with (1 := Xx).
    apply istrans_leNonnegativeRationals with c.
    pattern c at 2 ; rewrite (NQhalf_double c).
    now apply plusNonnegativeRationals_le_r.
    apply lt_leNonnegativeRationals.
    rewrite <- (minusNonnegativeRationals_zero_r x).
    apply Hx.
    now right.
  - destruct Hx as (x,(Xx,nXx)).
    case (isdecrel_leNonnegativeRationals (y + c / 2)%NRat x) ; intro Hxy.
    + assert (HY : Π y', coprod (Y y') (y' = 0%NRat) -> (y' < y + c / 2)%NRat).
      { intros y' [Yy' | Yy'].
        apply notge_ltNonnegativeRationals ; intro H ; apply nYy.
        now apply Y_bot with (1 := Yy').
        rewrite Yy'.
        now apply ispositive_plusNonnegativeRationals_r. }
      apply hinhpr ; right ; exists (x - (y + c / 2))%NRat ; split.
      * apply hinhpr.
        exists x ; split.
        exact Xx.
        intros y' Yy'.
        apply minusNonnegativeRationals_ltcompat_r.
        now apply HY.
        apply istrans_lt_le_ltNonnegativeRationals with (y + c / 2)%NRat.
        now apply HY.
        exact Hxy.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x',(Xx',Hx')).
        specialize (Hx' y Yy).
        revert Hx'.
        change (¬ (x - (y + c / 2) + c < x' - y)%NRat).
        apply (pr2 (notlt_geNonnegativeRationals _ _)).
        apply istrans_leNonnegativeRationals with ((x + c / 2) - y)%NRat.
        apply minusNonnegativeRationals_lecompat_l.
        apply lt_leNonnegativeRationals.
        apply notge_ltNonnegativeRationals ; intro H ; apply nXx.
        now apply X_bot with (1 := Xx').
        rewrite minusNonnegativeRationals_plus_exchange.
        apply_pr2 (plusNonnegativeRationals_lecompat_r y).
        rewrite minusNonnegativeRationals_plus_r.
        apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)%NRat).
        rewrite ! isassoc_plusNonnegativeRationals.
        rewrite <- NQhalf_double, minusNonnegativeRationals_plus_r.
        now apply isrefl_leNonnegativeRationals.
        apply istrans_leNonnegativeRationals with x.
        exact Hxy.
        now apply plusNonnegativeRationals_le_r.
        apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)%NRat).
        rewrite isassoc_plusNonnegativeRationals, <- NQhalf_double.
        apply istrans_leNonnegativeRationals with x.
        exact Hxy.
        now apply plusNonnegativeRationals_le_r.
        exact Hxy.
    + apply notge_ltNonnegativeRationals in Hxy.
      apply hinhpr ; left ; unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x',(Xx',Hx')).
      generalize (Hx' _ Yy).
      change (¬ (c < x' - y)%NRat) ; apply (pr2 (notlt_geNonnegativeRationals _ _)).
      case (isdecrel_leNonnegativeRationals y x') ; intro Hxy'.
      apply_pr2 (plusNonnegativeRationals_lecompat_r y).
      rewrite minusNonnegativeRationals_plus_r, iscomm_plusNonnegativeRationals, (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
      apply istrans_leNonnegativeRationals with (x + c / 2)%NRat.
      apply lt_leNonnegativeRationals ; apply notge_ltNonnegativeRationals ; intro ; apply nXx.
      now apply X_bot with (1 := Xx').
      apply plusNonnegativeRationals_lecompat_r.
      now apply lt_leNonnegativeRationals.
      exact Hxy'.
      apply notge_ltNonnegativeRationals in Hxy'.
      rewrite minusNonnegativeRationals_eq_zero.
      now apply isnonnegative_NonnegativeRationals.
      now apply lt_leNonnegativeRationals.
  - now apply hinhpr ; right.
Qed.

End Dcuts_minus.

Definition Dcuts_minus (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_minus_val (pr1 X) (pr1 Y))
           (Dcuts_minus_bot (pr1 X) (pr1 Y))
           (Dcuts_minus_open (pr1 X) (is_Dcuts_open X) (pr1 Y))
           (Dcuts_minus_error (pr1 X) (is_Dcuts_bot X) (is_Dcuts_error X)
                              (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_error Y)).

Lemma Dcuts_minus_correct_l:
  Π x y z : Dcuts, x = Dcuts_plus y z -> z = Dcuts_minus x y.
Proof.
  intros _ Y Z ->.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - intros Zr.
    generalize (is_Dcuts_open _ _ Zr) ; apply hinhuniv ; intros (q,(Zq,Hq)).
    apply ispositive_minusNonnegativeRationals in Hq.
    generalize (is_Dcuts_error Y _ Hq) ; apply hinhuniv ; intros [nYy | ].
    + apply hinhpr ; exists q ; split.
      * apply hinhpr ; left.
        now apply hinhpr ; right.
      * intros y [Yy | Hy0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r y).
        rewrite minusNonnegativeRationals_plus_r.
        apply minusNonnegativeRationals_ltcompat_l' with r.
        rewrite plusNonnegativeRationals_minus_l.
        now apply (Dcuts_finite Y).
        apply istrans_leNonnegativeRationals with (q - r).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Y).
        now apply minusNonnegativeRationals_le.
        rewrite Hy0, minusNonnegativeRationals_zero_r.
        now apply_pr2 ispositive_minusNonnegativeRationals.
    + intros (y,(Yy,Hy)).
      apply hinhpr.
      exists (y + q) ; split.
      apply hinhpr ; right.
      apply hinhpr ; exists (y,q) ; simpl ; repeat split.
      * exact Yy.
      * exact Zq.
      * intros y' [Yy' | Hy0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r y').
        rewrite minusNonnegativeRationals_plus_r.
        apply minusNonnegativeRationals_ltcompat_l' with r.
        rewrite plusNonnegativeRationals_minus_l.
        rewrite iscomm_plusNonnegativeRationals, <- minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals.
        now apply (Dcuts_finite Y).
        now apply lt_leNonnegativeRationals ; apply_pr2 ispositive_minusNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (y + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Y).
        apply plusNonnegativeRationals_lecompat_l.
        now apply minusNonnegativeRationals_le.
        rewrite Hy0, minusNonnegativeRationals_zero_r.
        apply istrans_lt_le_ltNonnegativeRationals with q.
        now apply_pr2 ispositive_minusNonnegativeRationals.
        now apply plusNonnegativeRationals_le_l.
  - apply hinhuniv ; intros (q,(YZq,Hq)).
    revert YZq ; apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [ Yq | Zq ] | intros ((qy,qz)) ; simpl ; intros (H,(Yq,Zq)) ].
    + apply fromempty, (isnonnegative_NonnegativeRationals' r).
      rewrite <- (minusNonnegativeRationals_eq_zero q _ (isrefl_leNonnegativeRationals _)).
      apply Hq.
      now left.
    + apply is_Dcuts_bot with (1 := Zq), lt_leNonnegativeRationals.
      rewrite <- (minusNonnegativeRationals_zero_r q).
      apply Hq.
      now right.
    + apply is_Dcuts_bot with (1 := Zq), lt_leNonnegativeRationals.
      rewrite <- (plusNonnegativeRationals_minus_l qy qz), <- H.
      apply Hq.
      now left.
Qed.
Lemma Dcuts_minus_correct_r:
  Π x y z : Dcuts, x = Dcuts_plus y z -> y = Dcuts_minus x z.
Proof.
  intros x y z Hx.
  apply Dcuts_minus_correct_l.
  rewrite Hx.
  now apply iscomm_Dcuts_plus.
Qed.
Lemma Dcuts_minus_eq_zero:
  Π x y : Dcuts, x <= y -> Dcuts_minus x y = 0.
Proof.
  intros X Y Hxy.
  apply Dcuts_eq_is_eq ; intros r ; split.
  - apply hinhuniv ; intros (x,(Xx,Hx)).
    simpl ; rewrite <- (minusNonnegativeRationals_eq_zero x _ (isrefl_leNonnegativeRationals _)).
    apply Hx.
    now left ; apply Hxy.
  - intro H.
    now apply fromempty ; apply (Dcuts_zero_empty r).
Qed.
Lemma Dcuts_minus_plus_r:
  Π x y z : Dcuts, z <= y -> x = Dcuts_minus y z -> y = Dcuts_plus x z.
Proof.
  intros _ Y Z Hyz ->.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - intros Yr.
    generalize (is_Dcuts_open _ _ Yr) ; apply hinhuniv ; intros (q,(Yq,Hq)).
    apply ispositive_minusNonnegativeRationals in Hq.
    generalize (is_Dcuts_error Z _ Hq).
    apply hinhuniv ; intros [nZ | ].
    + apply hinhpr ; left.
      apply hinhpr ; left.
      apply hinhpr.
      exists q ; split.
      exact Yq.
      intros z [Zz | Hz0].
      * apply_pr2 (plusNonnegativeRationals_ltcompat_r z).
        rewrite minusNonnegativeRationals_plus_r.
        apply (minusNonnegativeRationals_ltcompat_l' _ _ r).
        rewrite plusNonnegativeRationals_minus_l.
        now apply (Dcuts_finite Z).
        apply istrans_leNonnegativeRationals with (q - r).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        now apply minusNonnegativeRationals_le.
      * now rewrite Hz0, minusNonnegativeRationals_zero_r ; apply_pr2 ispositive_minusNonnegativeRationals.
    + intros (z,(Zz,nZz)).
      case (isdecrel_leNonnegativeRationals r z) ; intro Hzr.
      * apply hinhpr ; left.
        apply hinhpr ; right.
        now apply (is_Dcuts_bot _ _ Zz).
      * apply notge_ltNonnegativeRationals in Hzr ; apply lt_leNonnegativeRationals in Hzr.
        apply hinhpr ; right.
        apply hinhpr.
        exists (r - z , z) ; repeat split.
        simpl.
        now rewrite minusNonnegativeRationals_plus_r.
        apply hinhpr ; simpl.
        exists q ; split.
        exact Yq.
        intros z' [Zz' | Hz0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r z).
        rewrite minusNonnegativeRationals_plus_r.
        rewrite minusNonnegativeRationals_plus_exchange.
        apply_pr2 (plusNonnegativeRationals_ltcompat_r z').
        rewrite minusNonnegativeRationals_plus_r.
        apply (minusNonnegativeRationals_ltcompat_l' _ _ r) ; rewrite plusNonnegativeRationals_minus_l.
        rewrite <- minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals.
        now apply (Dcuts_finite Z).
        now apply lt_leNonnegativeRationals ; apply_pr2 ispositive_minusNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (z + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        rewrite iscomm_plusNonnegativeRationals, minusNonnegativeRationals_plus_exchange.
        now apply minusNonnegativeRationals_le.
        now apply lt_leNonnegativeRationals ; apply_pr2 ispositive_minusNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (z + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        pattern q at 2 ;
          rewrite <- (minusNonnegativeRationals_plus_r r q), iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        exact Hzr.
        now apply lt_leNonnegativeRationals ; apply_pr2 ispositive_minusNonnegativeRationals.
        exact Hzr.
        rewrite Hz0, minusNonnegativeRationals_zero_r.
        apply istrans_le_lt_ltNonnegativeRationals with r.
        now apply minusNonnegativeRationals_le.
        now apply_pr2 ispositive_minusNonnegativeRationals.
        exact Zz.
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [ YZr | Zr] | intros ((ryz,rz),(->,(YZr,Zr))) ].
    + revert YZr ; apply hinhuniv ; intros (y,(Yy,Hy)).
      apply (is_Dcuts_bot _ _ Yy).
      apply lt_leNonnegativeRationals ; rewrite <- (minusNonnegativeRationals_zero_r y).
      apply Hy.
      now right.
    + now apply Hyz.
    + simpl in Zr |- *.
      revert YZr ; apply hinhuniv ; simpl ; intros (y,(Yy,Hy)).
      apply (is_Dcuts_bot _ _ Yy).
      case (isdecrel_leNonnegativeRationals y rz) ; intro Hr.
      * apply fromempty, (isnonnegative_NonnegativeRationals' ryz).
        rewrite <- (minusNonnegativeRationals_eq_zero _ _ Hr).
        apply Hy.
        now left.
      * apply notge_ltNonnegativeRationals in Hr ; apply lt_leNonnegativeRationals in Hr.
        apply minusNonnegativeRationals_lecompat_l' with rz.
        exact Hr.
        rewrite plusNonnegativeRationals_minus_r.
        apply lt_leNonnegativeRationals, Hy.
        now left.
Qed.

Lemma Dcuts_minus_le :
  Π x y, Dcuts_minus x y <= x.
Proof.
  intros X Y r.
  apply hinhuniv ; intros (x,(Xx,Hx)).
  apply is_Dcuts_bot with (1 := Xx).
  apply lt_leNonnegativeRationals ; rewrite <- (minusNonnegativeRationals_zero_r x).
  apply Hx.
  now right.
Qed.

Lemma ispositive_Dcuts_minus :
  Π x y : Dcuts, (y < x) <-> (0 < Dcuts_minus x y).
Proof.
  intros X Y.
  split.
  - apply hinhuniv ; intros (x,(nYx,Xx)).
    generalize (is_Dcuts_open _ _ Xx) ; apply hinhfun ; intros (x',(Xx',Hx')).
    exists 0%NRat ; split.
    + now apply (isnonnegative_NonnegativeRationals' 0%NRat).
    + apply hinhpr.
      exists x' ; split.
      exact Xx'.
      intros y [Yy | ->].
      * apply ispositive_minusNonnegativeRationals.
        apply istrans_ltNonnegativeRationals with x.
        now apply (Dcuts_finite Y).
        exact Hx'.
      * rewrite minusNonnegativeRationals_zero_r.
        apply istrans_le_lt_ltNonnegativeRationals with x.
        now apply isnonnegative_NonnegativeRationals.
        exact Hx'.
  - apply hinhuniv ; intros (r,(_)).
    apply hinhfun ; intros (x,(Xx,Hx)).
    exists x ; split.
    + intros Yx ; apply (isnonnegative_NonnegativeRationals' r).
      rewrite <- (minusNonnegativeRationals_eq_zero x _ (isrefl_leNonnegativeRationals _)).
      now apply Hx ; left.
    + exact Xx.
Qed.

(** *** Dcuts_max *)

Section Dcuts_max.

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

Definition Dcuts_max_val : hsubtypes NonnegativeRationals :=
  λ r : NonnegativeRationals, X r ∨ Y r.

Lemma Dcuts_max_bot : Dcuts_def_bot Dcuts_max_val.
Proof.
  intros r Hr q Hqr.
  revert Hr ; apply hinhfun ; intros [Xr|Yr].
  - left ; now apply X_bot with (1 := Xr).
  - right ; now apply Y_bot with (1 := Yr).
Qed.

Lemma Dcuts_max_open : Dcuts_def_open Dcuts_max_val.
Proof.
  intros r ; apply hinhuniv ; intros [Xr | Yr].
  - generalize (X_open _ Xr).
    apply hinhfun ; intros (q,(Xq,Hq)).
    exists q ; split.
    now apply hinhpr ; left.
    exact Hq.
  - generalize (Y_open _ Yr).
    apply hinhfun ; intros (q,(Yq,Hq)).
    exists q ; split.
    now apply hinhpr ; right.
    exact Hq.
Qed.

Lemma Dcuts_max_error : Dcuts_def_error Dcuts_max_val.
Proof.
  intros c Hc.
  generalize (X_error _ Hc) (Y_error _ Hc) ; apply hinhfun2 ; intros [nXc | Hx] ; intros [nYc | Hy].
  - left ; unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xc | Yc].
    + now apply nXc.
    + now apply nYc.
  - right ; destruct Hy as (y,(Yy,nYy)).
    exists y ; split.
    + now apply hinhpr ; right.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xy | Yy'].
      * now apply nXc, X_bot with (1 := Xy), plusNonnegativeRationals_le_l.
      * now apply nYy.
  - right ; destruct Hx as (x,(Xx,nXx)).
    exists x ; split.
    + now apply hinhpr ; left.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xx' | Yx].
      * now apply nXx.
      * now apply nYc, Y_bot with (1 := Yx), plusNonnegativeRationals_le_l.
  - right ; revert Hx Hy ; intros (x,(Xx,nXx)) (y,(Yy,nYy)).
    exists (NQmax x y) ; split.
    + apply NQmax_case.
      * now apply hinhpr ; left.
      * now apply hinhpr ; right.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xxy | Yxy].
      * apply nXx, X_bot with (1 := Xxy).
        apply plusNonnegativeRationals_lecompat_r.
        now apply NQmax_le_l.
      * apply nYy, Y_bot with (1 := Yxy).
        apply plusNonnegativeRationals_lecompat_r.
        now apply NQmax_le_r.
Qed.

End Dcuts_max.

Definition Dcuts_max (X Y : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_max_val (pr1 X) (pr1 Y))
           (Dcuts_max_bot (pr1 X) (is_Dcuts_bot X)
                          (pr1 Y) (is_Dcuts_bot Y))
           (Dcuts_max_open (pr1 X) (is_Dcuts_open X)
                           (pr1 Y) (is_Dcuts_open Y))
           (Dcuts_max_error (pr1 X) (is_Dcuts_bot X) (is_Dcuts_error X)
                            (pr1 Y) (is_Dcuts_bot Y) (is_Dcuts_error Y)).

Lemma iscomm_Dcuts_max :
  Π x y : Dcuts, Dcuts_max x y = Dcuts_max y x.
Proof.
  intros x y.
  apply Dcuts_eq_is_eq ; intros r.
  split ; apply islogeqcommhdisj.
Qed.

Lemma Dcuts_max_le_l :
  Π x y : Dcuts, x <= Dcuts_max x y.
Proof.
  intros x y r Xr.
  apply hinhpr.
  now left.
Qed.
Lemma Dcuts_max_le_r :
  Π x y : Dcuts, y <= Dcuts_max x y.
Proof.
  intros x y r Xr.
  apply hinhpr.
  now right.
Qed.

Lemma Dcuts_max_carac_l :
  Π x y : Dcuts, y <= x -> Dcuts_max x y = x.
Proof.
  intros x y Hxy.
  apply Dcuts_eq_is_eq ; intros r ; split.
  apply hinhuniv ; intros [Xr|Yr].
  - exact Xr.
  - now apply Hxy.
  - intros Xr.
    now apply hinhpr ; left.
Qed.
Lemma Dcuts_max_carac_r :
  Π x y : Dcuts, x <= y -> Dcuts_max x y = y.
Proof.
  intros x y Hxy.
  rewrite iscomm_Dcuts_max.
  now apply Dcuts_max_carac_l.
Qed.

Lemma Dcuts_minus_plus_max :
  Π x y : Dcuts, Dcuts_plus (Dcuts_minus x y) y = Dcuts_max x y.
Proof.
  intros X Y.
  apply Dcuts_eq_is_eq ; intros r ; split.
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [XYr | Yr] | intros ((rxy,ry),(->,(XYr,Yr)))].
    + apply hinhpr ; left.
      revert XYr ; now apply Dcuts_minus_le.
    + now apply hinhpr ; right.
    + revert XYr ; apply hinhfun ; intros (x,(Xx,Hx)) ; simpl in * |- *.
      left ; apply is_Dcuts_bot with (1 := Xx).
      apply lt_leNonnegativeRationals, minusNonnegativeRationals_ltcompat_l' with ry.
      rewrite plusNonnegativeRationals_minus_r.
      apply Hx.
      now left.
  - apply hinhuniv ; intros [Xr|Yr].
    + generalize (is_Dcuts_open _ _ Xr) ; apply hinhuniv ; intros (x,(Xx,Hx)).
      apply ispositive_minusNonnegativeRationals in Hx.
      generalize (is_Dcuts_error Y _ Hx) ; apply hinhuniv ;
      intros [nYx | Hyx ] ; apply_pr2_in ispositive_minusNonnegativeRationals Hx.
      * rewrite <- (Dcuts_minus_plus_r (Dcuts_minus X Y) X Y).
        exact Xr.
        apply Dcuts_lt_le_rel.
        apply hinhpr ; exists (x - r) ; split.
        exact nYx.
        apply is_Dcuts_bot with (1 := Xx).
        now apply minusNonnegativeRationals_le.
        reflexivity.
      * destruct Hyx as (y,(Yy,nYy)).
        rewrite iscomm_plusNonnegativeRationals, minusNonnegativeRationals_plus_exchange in nYy.
        2: now apply lt_leNonnegativeRationals.
        case (isdecrel_leNonnegativeRationals r y) ; intros Hle.
        { apply hinhpr ; left.
          apply hinhpr ; right.
          now apply is_Dcuts_bot with (1 := Yy). }
        apply notge_ltNonnegativeRationals in Hle.
        rewrite <- (Dcuts_minus_plus_r (Dcuts_minus X Y) X Y).
        exact Xr.
        apply Dcuts_lt_le_rel.
        apply hinhpr ; exists ((x + y) - r) ; split.
        exact nYy.
        apply is_Dcuts_bot with (1 := Xx).
        pattern x at 2 ;
          rewrite <- (plusNonnegativeRationals_minus_r r x).
        apply minusNonnegativeRationals_lecompat_l.
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals.
        reflexivity.
    + apply hinhpr ; left.
      now apply hinhpr ; right.
Qed.

Lemma Dcuts_max_le :
  Π x y z, x <= z -> y <= z -> Dcuts_max x y <= z.
Proof.
  intros x y z Hx Hy r.
  apply hinhuniv ; intros [Xr|Yr].
  now apply Hx.
  now apply Hy.
Qed.
Lemma Dcuts_max_lt :
  Π x y z : Dcuts, x < z -> y < z -> Dcuts_max x y < z.
Proof.
  intros x y z.
  apply hinhfun2 ; intros (rx,(Xrx,Zrx)) (ry,(Yry,Zry)).
  exists (NQmax rx ry) ; split.
  - apply NQmax_case_strong ; intro Hr.
    + intro Hr' ; apply Yry.
      revert Hr' ; apply hinhuniv ; intros [Xr | Yr].
      now apply fromempty, Xrx.
      now apply is_Dcuts_bot with (1 := Yr).
    + intro Hr' ; apply Xrx.
      revert Hr' ; apply hinhuniv ; intros [Xr | Yr].
      now apply is_Dcuts_bot with (1 := Xr).
      now apply fromempty, Xrx.
  - now apply NQmax_case.
Qed.

Lemma isassoc_Dcuts_max :
  isassoc Dcuts_max.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq.
  intros r.
  split.
  - apply hinhuniv.
    intros [ | Zr].
    + apply hinhfun.
      intros [Xr | Yr].
      * now left.
      * right.
        apply hinhpr.
        now left.
    + apply hinhpr.
      right.
      apply hinhpr.
      now right.
  - apply hinhuniv.
    intros [ Xr | ].
    + apply hinhpr.
      left.
      apply hinhpr.
      now left.
    + apply hinhfun.
      intros [Yr | Zr].
      * left.
        apply hinhpr.
        now right.
      * now right.
Qed.

Lemma isldistr_Dcuts_max_mult :
  isldistr Dcuts_max Dcuts_mult.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv.
    intros ((rz,rxy)) ; simpl fst ; simpl snd ; intros (->,(Zr)).
    apply hinhfun.
    intros [Xr | Yr].
    + left.
      apply hinhpr.
      now exists (rz,rxy).
    + right.
      apply hinhpr.
      now exists (rz,rxy).
  - apply hinhuniv.
    intros [ | ].
    + apply hinhfun.
      intros ((rz,rx)) ; simpl fst ; simpl snd ; intros (->,(Zr,Xr)).
      exists (rz,rx).
      repeat split.
      exact Zr.
      apply hinhpr.
      now left.
    + apply hinhfun.
      intros ((rz,ry)) ; simpl fst ; simpl snd ; intros (->,(Zr,Yr)).
      exists (rz,ry).
      repeat split.
      exact Zr.
      apply hinhpr.
      now right.
Qed.
Lemma isrdistr_Dcuts_max_mult :
  isrdistr Dcuts_max Dcuts_mult.
Proof.
  intros x y z.
  rewrite !(iscomm_Dcuts_mult _ z).
  now apply isldistr_Dcuts_max_mult.
Qed.

Lemma isldistr_Dcuts_max_plus :
  isldistr Dcuts_max Dcuts_plus.
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [ intros [Zr | ]
    | intros ((rz,rxy)) ; simpl fst ; simpl snd ; intros (->,(Zr)) ].
    + apply hinhpr.
      left.
      apply hinhpr.
      left.
      apply hinhpr.
      now left.
    + apply hinhfun.
      intros [Xr | Yr].
      * left.
        apply hinhpr.
        left.
        apply hinhpr.
        now right.
      * right.
        apply hinhpr.
        left.
        apply hinhpr.
        now right.
    + apply hinhfun.
      intros [Xr | Yr].
      * left.
        apply hinhpr.
        right.
        apply hinhpr.
        now exists (rz,rxy).
      * right.
        apply hinhpr.
        right.
        apply hinhpr.
        now exists (rz,rxy).
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; intros [ | ].
    + apply hinhfun.
      intros [Zr | Xr] ; left.
      * apply hinhpr.
        now left.
      * apply hinhpr.
        right.
        apply hinhpr.
        now left.
    + apply hinhfun ; intros ((rz,rx)) ; simpl fst ; simpl snd ; intros (->,(Zr,Xr)).
      right.
      apply hinhpr.
      exists (rz, rx).
      repeat split.
      exact Zr.
      apply hinhpr.
      now left.
    + apply hinhfun.
      intros [Zr | Yr] ; left.
      * apply hinhpr.
        now left.
      * apply hinhpr.
        right.
        apply hinhpr.
        now right.
    + apply hinhfun ; intros ((rz,ry)) ; simpl fst ; simpl snd ; intros (->,(Zr,Yr)).
      right.
      apply hinhpr.
      exists (rz, ry).
      repeat split.
      exact Zr.
      apply hinhpr.
      now right.
Qed.

Lemma Dcuts_max_plus :
  Π x y : Dcuts,
    (0 < x -> y = 0) ->
    Dcuts_max x y = Dcuts_plus x y.
Proof.
  intros x y H.
  apply Dcuts_le_ge_eq.
  - intros r H0.
    apply hinhpr.
    left.
    exact H0.
  - intros r.
    apply hinhuniv.
    intros [H0 | ].
    exact H0.
    apply hinhuniv.
    intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr)).
    apply fromempty.
    refine (Dcuts_zero_empty _ _).
    rewrite <- H.
    apply Yr.
    apply hinhpr.
    exists rx.
    split.
    apply Dcuts_zero_empty.
    exact Xr.
Qed.

(** *** Dcuts_half *)

Lemma Dcuts_two_ap_zero : Dcuts_two ≠ 0.
Proof.
  apply isapfun_NonnegativeRationals_to_Dcuts'.
  apply gtNonnegativeRationals_noteq.
  exact ispositive_twoNonnegativeRationals.
Qed.

Section Dcuts_half.

Context (X : hsubtypes NonnegativeRationals)
        (X_bot : Dcuts_def_bot X)
        (X_open : Dcuts_def_open X)
        (X_error : Dcuts_def_error X).

Definition Dcuts_half_val : hsubtypes NonnegativeRationals :=
  λ r, X (r + r).
Lemma Dcuts_half_bot : Dcuts_def_bot Dcuts_half_val.
Proof.
  intros r Hr q Hq.
  apply X_bot with (1 := Hr).
  eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_lecompat_l, Hq.
  now apply plusNonnegativeRationals_lecompat_r, Hq.
Qed.
Lemma Dcuts_half_open : Dcuts_def_open Dcuts_half_val.
Proof.
  intros r Hr.
  generalize (X_open _ Hr).
  apply hinhfun ; intros (q,(Hq,Hrq)).
  exists (q / 2)%NRat ; split.
  - unfold Dcuts_half_val.
    now rewrite <- NQhalf_double.
  - apply_pr2 (multNonnegativeRationals_ltcompat_l 2%NRat).
    exact ispositive_twoNonnegativeRationals.
    rewrite (NQhalf_double r), isldistr_mult_plusNonnegativeRationals, !multdivNonnegativeRationals.
    exact Hrq.
    exact ispositive_twoNonnegativeRationals.
    exact ispositive_twoNonnegativeRationals.
Qed.
Lemma Dcuts_half_error : Dcuts_def_error Dcuts_half_val.
Proof.
  intros c Hc.
  assert (Hc0 : (0 < c + c)%NRat)
    by (now apply ispositive_plusNonnegativeRationals_l).
  generalize (X_error _ Hc0) ; apply hinhfun ; intros [Hx|Hx].
  - left ; exact Hx.
  - right ; destruct Hx as (r,(Xr,nXr)).
    exists (r / 2)%NRat ; split.
    + unfold Dcuts_half_val.
      now rewrite <- NQhalf_double.
    + intro H ; apply nXr.
      apply X_bot with (1 := H).
      pattern r at 1 ;
        rewrite (NQhalf_double r), !isassoc_plusNonnegativeRationals.
      apply plusNonnegativeRationals_lecompat_l.
      rewrite iscomm_plusNonnegativeRationals, !isassoc_plusNonnegativeRationals.
      apply plusNonnegativeRationals_lecompat_l.
      rewrite iscomm_plusNonnegativeRationals.
      now apply isrefl_leNonnegativeRationals.
Qed.

End Dcuts_half.

Definition Dcuts_half (x : Dcuts) : Dcuts :=
  mk_Dcuts (Dcuts_half_val (pr1 x))
           (Dcuts_half_bot (pr1 x) (is_Dcuts_bot x))
           (Dcuts_half_open (pr1 x) (is_Dcuts_open x))
           (Dcuts_half_error (pr1 x) (is_Dcuts_bot x) (is_Dcuts_error x)).

Lemma Dcuts_half_le :
  Π x : Dcuts, Dcuts_half x <= x.
Proof.
  intros x.
  intros r Hr.
  apply is_Dcuts_bot with (1 := Hr).
  now apply plusNonnegativeRationals_le_l.
Qed.

Lemma isdistr_Dcuts_half_plus :
  Π x y : Dcuts, Dcuts_half (Dcuts_plus x y) = Dcuts_plus (Dcuts_half x) (Dcuts_half y).
Proof.
  intros x y.
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv ; intros [ | ] ; apply hinhfun ; [intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
    + left.
      apply hinhpr.
      left.
      exact Xr.
    + left.
      apply hinhpr.
      right.
      exact Yr.
    + right.
      apply hinhpr.
      exists (rx / 2%NRat, ry/2%NRat).
      unfold Dcuts_half_val ; simpl ; repeat split.
      * unfold divNonnegativeRationals.
        rewrite <- isrdistr_mult_plusNonnegativeRationals, <- Hr, isrdistr_mult_plusNonnegativeRationals.
        now apply NQhalf_double.
      * rewrite <- NQhalf_double.
        exact Xr.
      * rewrite <- NQhalf_double.
        exact Yr.
  - apply hinhuniv ; intros [ | ] ; apply hinhfun ; [intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr))].
    + left.
      apply hinhpr.
      left.
      exact Xr.
    + left.
      apply hinhpr.
      right.
      exact Yr.
    + right.
      apply hinhpr.
      exists (rx + rx, ry + ry).
      simpl ; repeat split.
      * rewrite !isassoc_plusNonnegativeRationals.
        apply maponpaths.
        rewrite iscomm_plusNonnegativeRationals, isassoc_plusNonnegativeRationals.
        reflexivity.
      * exact Xr.
      * exact Yr.
Qed.
Lemma Dcuts_half_double :
  Π x : Dcuts, x = Dcuts_plus (Dcuts_half x) (Dcuts_half x).
Proof.
  intros x.
  rewrite  <- isdistr_Dcuts_half_plus.
  apply Dcuts_eq_is_eq ; split.
  - intros Hr.
    apply hinhpr ; right.
    apply hinhpr ; exists (r,r).
    now repeat split.
  - apply hinhuniv ; intros [|] ; apply hinhuniv ; [intros [ | ] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr)) ].
    + now apply Dcuts_half_le.
    + now apply Dcuts_half_le.
    + case (isdecrel_ltNonnegativeRationals r rx) ; intro Hrx.
      apply is_Dcuts_bot with (1 := Xr).
      now apply lt_leNonnegativeRationals.
      apply is_Dcuts_bot with (1 := Yr).
      apply_pr2 (plusNonnegativeRationals_lecompat_l r).
      rewrite Hr.
      apply plusNonnegativeRationals_lecompat_r.
      now apply notlt_geNonnegativeRationals.
Qed.

Lemma Dcuts_half_correct :
  Π x, Dcuts_half x = Dcuts_mult x (Dcuts_inv Dcuts_two Dcuts_two_ap_zero).
Proof.
  intros x.
  pattern x at 2 ; rewrite (Dcuts_half_double x).
  rewrite Dcuts_plus_double, iscomm_Dcuts_mult, <- isassoc_Dcuts_mult, islinv_Dcuts_inv, islunit_Dcuts_mult_one.
  reflexivity.
Qed.

Lemma ispositive_Dcuts_half:
  Π x : Dcuts, (0 < x) <-> (0 < Dcuts_half x).
Proof.
  intros.
  rewrite Dcuts_half_correct.
  pattern 0 at 2 ; rewrite <- (islabsorb_Dcuts_mult_zero (Dcuts_inv Dcuts_two Dcuts_two_ap_zero)).
  split.
  - intro Hx0.
    apply Dcuts_mult_ltcompat_l.
    apply Dcuts_mult_ltcompat_l' with Dcuts_two.
    rewrite islabsorb_Dcuts_mult_zero, islinv_Dcuts_inv.
    unfold Dcuts_zero, Dcuts_one.
    apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux 0%NRat 1%NRat)).
    now apply ispositive_oneNonnegativeRationals.
    exact Hx0.
  - now apply Dcuts_mult_ltcompat_l'.
Qed.

(** ** Locatedness *)

Lemma Dcuts_locatedness :
  Π X : Dcuts, Π p q : NonnegativeRationals, (p < q)%NRat -> p ∈ X ∨ ¬ (q ∈ X).
Proof.
  intros X p q Hlt.
  apply ispositive_minusNonnegativeRationals in Hlt.
  generalize (is_Dcuts_error X _ Hlt).
  apply_pr2_in ispositive_minusNonnegativeRationals Hlt.
  apply hinhuniv ; intros [Xr | ].
  - apply hinhpr ; right.
    intro H ; apply Xr.
    apply is_Dcuts_bot with (1 := H).
    now apply minusNonnegativeRationals_le.
  - intros (r,(Xr,nXr)).
    destruct (isdecrel_leNonnegativeRationals p r) as [Hle | Hnle].
    + apply hinhpr ; left.
      now apply is_Dcuts_bot with (1 := Xr).
    + apply notge_ltNonnegativeRationals in Hnle.
      apply hinhpr ; right.
      intro H ; apply nXr.
      apply is_Dcuts_bot with (1 := H).
      apply_pr2 (plusNonnegativeRationals_lecompat_r p).
      rewrite isassoc_plusNonnegativeRationals, minusNonnegativeRationals_plus_r, iscomm_plusNonnegativeRationals.
      apply plusNonnegativeRationals_lecompat_l.
      now apply lt_leNonnegativeRationals.
      now apply lt_leNonnegativeRationals.
Qed.

(** ** Limits of Cauchy sequences *)

Section Dcuts_lim.

Context (U : nat -> hsubtypes NonnegativeRationals)
        (U_bot : Π n : nat, Dcuts_def_bot (U n))
        (U_open : Π n : nat, Dcuts_def_open (U n))
        (U_error : Π n : nat, Dcuts_def_error (U n)).

Context (U_cauchy :
           Π eps : NonnegativeRationals,
                   (0 < eps)%NRat ->
                   hexists
                     (λ N : nat,
                            Π n m : nat, N ≤ n -> N ≤ m -> (Π r, U n r -> Dcuts_plus_val (U m) (λ q, (q < eps)%NRat) r) × (Π r, U m r -> Dcuts_plus_val (U n) (λ q, (q < eps)%NRat) r))).

Definition Dcuts_lim_cauchy_val : hsubtypes NonnegativeRationals :=
λ r : NonnegativeRationals, hexists (λ c : NonnegativeRationals, (0 < c)%NRat × Σ N : nat, Π n : nat, N ≤ n -> U n (r + c)).

Lemma Dcuts_lim_cauchy_bot : Dcuts_def_bot Dcuts_lim_cauchy_val.
Proof.
  intros r Hr q Hq.
  revert Hr ; apply hinhfun ; intros (c,(Hc,(N,Hr))).
  exists c ; split.
  exact Hc.
  exists N ; intros n Hn.
  apply (U_bot n) with (1 := Hr n Hn).
  apply plusNonnegativeRationals_lecompat_r.
  exact Hq.
Qed.
Lemma Dcuts_lim_cauchy_open : Dcuts_def_open Dcuts_lim_cauchy_val.
Proof.
  intros r.
  apply hinhfun ; intros (c,(Hc,(N,Hr))).
  exists (r + (c / 2))%NRat ; split.
  - apply hinhpr.
    exists (c / 2)%NRat ; split.
    + now apply ispositive_NQhalf, Hc.
    + exists N ; intros n Hn.
      rewrite isassoc_plusNonnegativeRationals, <- NQhalf_double.
      now apply Hr.
  - now apply plusNonnegativeRationals_lt_r, ispositive_NQhalf.
Qed.
Lemma Dcuts_lim_cauchy_error : Dcuts_def_error Dcuts_lim_cauchy_val.
Proof.
  intros c Hc.
  apply ispositive_NQhalf, ispositive_NQhalf in Hc.
  generalize (U_cauchy _ Hc) ; clear U_cauchy ; apply hinhuniv ; intros (N,Hu).
  generalize (λ n Hn, Hu n N Hn (isreflnatleh _)) ; clear Hu ; intro Hu.
  generalize (U_error N _ Hc).
  apply hinhuniv ; intros [HuN | HuN].
  - apply hinhpr ; left.
    intro ; apply HuN ; clear HuN.
    revert X ; apply hinhuniv ; intros (eps,(Heps,(N',HuN'))).
    destruct (natgthorleh N N') as [HN | HN].
    + apply natlthtoleh in HN.
      apply (U_bot N) with (1 := HuN' _ HN).
      pattern c at 2 ;
        rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
      pattern (c / 2)%NRat at 2 ;
        rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
      now apply plusNonnegativeRationals_le_r.
    + specialize (HuN' _ (isreflnatleh _)).
      generalize (pr1 (Hu _ HN) _ HuN') ; clear Hu HuN'.
      apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [ intros [H | H] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
      * apply (U_bot N) with (1 := H).
        pattern c at 2 ;
          rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
      pattern (c / 2)%NRat at 2 ;
        rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
        now apply plusNonnegativeRationals_le_r.
      * apply fromempty.
        revert H.
        apply_pr2 notlt_geNonnegativeRationals.
        pattern c at 2 ;
          rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
        pattern (c / 2)%NRat at 2 ;
          rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
        now apply plusNonnegativeRationals_le_r.
      * apply (U_bot N) with (1 := Xr).
        apply_pr2 (plusNonnegativeRationals_lecompat_r ry).
        rewrite <- Hr.
        pattern c at 2 ;
          rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
        pattern (c / 2)%NRat at 2 ;
          rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        apply istrans_leNonnegativeRationals with (c / 2 / 2)%NRat.
        now apply lt_leNonnegativeRationals.
        now apply plusNonnegativeRationals_le_r.
  - destruct HuN as (q,(UNq,nUNq)).
    case (isdecrel_leNonnegativeRationals q (c / 2)%NRat) ; intros Hq.
    + apply hinhpr ; left.
      intro ; apply nUNq ; clear nUNq UNq.
      revert X ; apply hinhuniv ; intros (eps,(Heps,(N',HuN'))).
      destruct (natgthorleh N N') as [HN | HN].
      * apply natlthtoleh in HN.
        apply (U_bot N) with (1 := HuN' _ HN).
        pattern c at 2 ;
          rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
        apply istrans_leNonnegativeRationals with (c / 2 + c / 2 / 2)%NRat.
        apply plusNonnegativeRationals_lecompat_r.
        exact Hq.
        apply plusNonnegativeRationals_lecompat_l.
        pattern (c / 2)%NRat at 2 ;
          rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
        now apply plusNonnegativeRationals_le_r.
      * specialize (HuN' _ (isreflnatleh _)).
        generalize (pr1 (Hu _ HN) _ HuN') ; clear Hu HuN'.
        apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [ intros [H | H] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
        { apply (U_bot N) with (1 := H).
          pattern c at 2 ;
            rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals, iscomm_plusNonnegativeRationals.
          apply istrans_leNonnegativeRationals with (c / 2 / 2 + c / 2)%NRat.
          apply plusNonnegativeRationals_lecompat_l.
          exact Hq.
          rewrite iscomm_plusNonnegativeRationals.
          apply plusNonnegativeRationals_lecompat_l.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
          now apply plusNonnegativeRationals_le_r. }
        { apply fromempty.
          revert H.
          apply_pr2 notlt_geNonnegativeRationals.
          pattern c at 2 ;
            rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
          now apply plusNonnegativeRationals_le_r. }
        { apply (U_bot N) with (1 := Xr).
          apply_pr2 (plusNonnegativeRationals_lecompat_r ry).
          rewrite <- Hr.
          pattern c at 2 ;
            rewrite (NQhalf_double c), !isassoc_plusNonnegativeRationals.
          eapply istrans_leNonnegativeRationals.
          apply plusNonnegativeRationals_lecompat_r.
          now apply Hq.
          apply plusNonnegativeRationals_lecompat_l.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
          apply plusNonnegativeRationals_lecompat_l.
          apply istrans_leNonnegativeRationals with (c / 2 / 2)%NRat.
          now apply lt_leNonnegativeRationals.
          now apply plusNonnegativeRationals_le_r. }
    +  apply hinhpr ; right.
      apply notge_ltNonnegativeRationals in Hq.
      exists (q - c / 2)%NRat ; split.
      * apply hinhpr.
        exists (c / 2 / 2)%NRat ; split.
        exact Hc.
        exists N ; intros n Hn.
        generalize (pr2 (Hu _ Hn) _ UNq).
        apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
        { apply (U_bot n) with (1 := Xr).
          pattern q at 2 ;
            rewrite <- (minusNonnegativeRationals_plus_r (c / 2)%NRat q).
          apply plusNonnegativeRationals_lecompat_l.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat).
          now apply plusNonnegativeRationals_le_r.
          now apply lt_leNonnegativeRationals. }
        { apply fromempty.
          revert Yr.
          apply_pr2 notlt_geNonnegativeRationals.
          eapply istrans_leNonnegativeRationals, lt_leNonnegativeRationals, Hq.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat).
          now apply plusNonnegativeRationals_le_r. }
        { apply (U_bot n) with (1 := Xr).
          apply_pr2 (plusNonnegativeRationals_lecompat_r ry).
          rewrite <- Hr.
          pattern q at 2 ;
            rewrite <- (minusNonnegativeRationals_plus_r (c / 2)%NRat q), isassoc_plusNonnegativeRationals.
          apply plusNonnegativeRationals_lecompat_l.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat).
          apply plusNonnegativeRationals_lecompat_l.
          now apply lt_leNonnegativeRationals.
          now apply lt_leNonnegativeRationals. }
      * intro ; apply nUNq ; clear nUNq.
        revert X ; apply hinhuniv ; intros (eps,(Heps,(N',HuN))).
        destruct (natgthorleh N N') as [HN | HN].
        { apply natlthtoleh in HN.
          apply (U_bot N) with (1 := HuN _ HN).
          pattern c at 3 ;
            rewrite (NQhalf_double c), <- isassoc_plusNonnegativeRationals, minusNonnegativeRationals_plus_r.
          pattern (c / 2)%NRat at 2 ;
            rewrite (NQhalf_double (c / 2)%NRat), !isassoc_plusNonnegativeRationals, <- (isassoc_plusNonnegativeRationals q (c / 2 / 2)%NRat).
          now apply plusNonnegativeRationals_le_r.
          now apply lt_leNonnegativeRationals. }
        { specialize (HuN _ (isreflnatleh _)).
          generalize (pr1 (Hu _ HN) _ HuN) ; clear Hu HuN.
          apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [ intros [H | H] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
          - apply (U_bot N) with (1 := H).
            pattern q at 1 ;
            rewrite <- (minusNonnegativeRationals_plus_r (c / 2)%NRat q), !isassoc_plusNonnegativeRationals.
            apply plusNonnegativeRationals_lecompat_l.
            pattern c at 3 ;
              rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
            apply plusNonnegativeRationals_lecompat_l.
            pattern (c / 2)%NRat at 2 ;
              rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
            now apply plusNonnegativeRationals_le_r.
            now apply lt_leNonnegativeRationals.
          -  apply fromempty.
             revert H.
             apply_pr2 notlt_geNonnegativeRationals.
             eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_le_r.
             eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_le_l.
             pattern c at 2 ;
               rewrite (NQhalf_double c).
             pattern (c / 2)%NRat at 2 ;
               rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
             now apply plusNonnegativeRationals_le_r.
          - apply (U_bot N) with (1 := Xr).
            apply_pr2 (plusNonnegativeRationals_lecompat_r ry).
            rewrite <- Hr.
            pattern q at 1 ;
              rewrite <- (minusNonnegativeRationals_plus_r (c / 2)%NRat q), !isassoc_plusNonnegativeRationals.
            apply plusNonnegativeRationals_lecompat_l.
            pattern c at 3 ;
              rewrite (NQhalf_double c), isassoc_plusNonnegativeRationals.
            apply plusNonnegativeRationals_lecompat_l.
            pattern (c / 2)%NRat at 2 ;
              rewrite (NQhalf_double (c / 2)%NRat), isassoc_plusNonnegativeRationals.
            apply plusNonnegativeRationals_lecompat_l.
            apply istrans_leNonnegativeRationals with (c / 2 / 2)%NRat.
            now apply lt_leNonnegativeRationals.
            now apply plusNonnegativeRationals_le_r.
            now apply lt_leNonnegativeRationals. }
Qed.

End Dcuts_lim.

Definition Dcuts_Cauchy_seq (u : nat -> Dcuts) : hProp
  := hProppair (Π eps : Dcuts,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            Π n m : nat, N ≤ n -> N ≤ m -> u n < Dcuts_plus (u m) eps × u m < Dcuts_plus (u n) eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).
Definition is_Dcuts_lim_seq (u : nat -> Dcuts) (l : Dcuts) : hProp
  := hProppair (Π eps : Dcuts,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            Π n : nat, N ≤ n -> u n < Dcuts_plus l eps × l < Dcuts_plus (u n) eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).

Definition Dcuts_lim_cauchy_seq (u : nat -> Dcuts) (Hu : Dcuts_Cauchy_seq u) : Dcuts.
Proof.
  intros U HU.
  exists (Dcuts_lim_cauchy_val (fun n => pr1 (U n))).
  repeat split.
  - apply Dcuts_lim_cauchy_bot.
    intro ; now apply is_Dcuts_bot.
  - apply Dcuts_lim_cauchy_open.
  - apply Dcuts_lim_cauchy_error.
    + intro ; now apply is_Dcuts_bot.
    + intro ; now apply is_Dcuts_error.
    + intros eps Heps.
      assert (0 < NonnegativeRationals_to_Dcuts eps)
        by (now apply_pr2 isapfun_NonnegativeRationals_to_Dcuts_aux).
      generalize (HU _ X) ; clear HU.
      apply hinhfun ; intros HU.
      exists (pr1 HU) ; intros n m Hn Hm.
      set (pr2 HU n m Hn Hm) ; clearbody d ; clear -d ; rename d into HU.
      split.
      * now refine (Dcuts_lt_le_rel _ _ (pr1 HU)).
      * now refine (Dcuts_lt_le_rel _ _ (pr2 HU)).
Defined.

Lemma Dcuts_Cauchy_seq_impl_ex_lim_seq (u : nat -> Dcuts) (Hu : Dcuts_Cauchy_seq u) :
  is_Dcuts_lim_seq u (Dcuts_lim_cauchy_seq u Hu).
Proof.
  intros U HU eps.
  apply hinhuniv ; intros (c',(_,Hc')).
  generalize (is_Dcuts_open _ _ Hc').
  apply hinhuniv ; intros (c,(Hc,Hcc')).
  assert (Hc0 : (0 < c)%NRat).
  { eapply istrans_le_lt_ltNonnegativeRationals, Hcc'.
    now apply isnonnegative_NonnegativeRationals. }
  clear c' Hc' Hcc'.
  apply ispositive_NQhalf in Hc0.
  generalize (HU _ (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _) Hc0)).
  apply hinhfun ; intros (N,Hu).
  exists N ; intros n Hn.
  generalize (λ n Hn, Hu n N Hn (isreflnatleh _)) ; clear Hu ; intros Hu.
  split.
  - eapply istrans_Dcuts_lt_le_rel.
    now apply (Hu n Hn).
    rewrite (Dcuts_half_double eps), <- isassoc_Dcuts_plus.
    eapply istrans_Dcuts_le_rel, Dcuts_plus_lecompat_l.
    + apply Dcuts_plus_lecompat_r.
      intros r Hr.
      simpl.
      apply is_Dcuts_bot with (1 := Hc).
      rewrite (NQhalf_double c).
      now apply lt_leNonnegativeRationals, plusNonnegativeRationals_ltcompat ; apply Hr.
    + intros r Hr.
      case (isdecrel_ltNonnegativeRationals r (c / 2)%NRat) ; intro Hrc.
      * apply hinhpr ; left.
        apply hinhpr ; right.
        apply is_Dcuts_bot with (1 := Hc).
        rewrite (NQhalf_double c).
        now apply lt_leNonnegativeRationals, plusNonnegativeRationals_ltcompat ; apply Hrc.
      * apply notlt_geNonnegativeRationals in Hrc.
        generalize (is_Dcuts_open _ _ Hr).
        apply hinhuniv ; intros (q,(Hq,Hrq)).
        apply hinhpr ; right.
        apply hinhpr ; exists (r - c / 2%NRat, c / 2%NRat) ; repeat split.
        now simpl ; rewrite minusNonnegativeRationals_plus_r.
        apply hinhpr ; exists (q - r) ; split.
        apply ispositive_minusNonnegativeRationals, Hrq.
        exists N ; intros m Hm.
        simpl.
        rewrite minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals, minusNonnegativeRationals_plus_r.
        generalize (Dcuts_lt_le_rel _ _ (pr2 (Hu m Hm)) _ Hq) ; clear Hu.
        apply hinhuniv ; intros [|] ; apply hinhuniv ; [ intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr))].
        apply is_Dcuts_bot with (1 := Xr).
        now apply minusNonnegativeRationals_le.
        simpl in Yr.
        apply_pr2_in notge_ltNonnegativeRationals Yr.
        apply fromempty, Yr.
        apply istrans_leNonnegativeRationals with r.
        exact Hrc.
        now apply lt_leNonnegativeRationals.
        apply is_Dcuts_bot with (1 := Xr).
        apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)%NRat).
        rewrite minusNonnegativeRationals_plus_r.
        now apply plusNonnegativeRationals_lecompat_l, lt_leNonnegativeRationals.
        apply istrans_leNonnegativeRationals with r.
        exact Hrc.
        now apply lt_leNonnegativeRationals.
        now apply lt_leNonnegativeRationals.
        exact Hrc.
        simpl ; unfold Dcuts_half_val.
        now rewrite <- NQhalf_double.
  - apply istrans_Dcuts_le_lt_rel with (Dcuts_plus (U N) (Dcuts_half eps)).
    + intros r.
      apply hinhuniv ; intros (c',(Hc'0,(N',Hc'))).
      case (isdecrel_ltNonnegativeRationals r (c / 2)%NRat) ; intro Hrc.
      * apply hinhpr ; left.
        apply hinhpr ; right.
        apply is_Dcuts_bot with (1 := Hc).
        rewrite (NQhalf_double c).
        now apply lt_leNonnegativeRationals, plusNonnegativeRationals_ltcompat ; apply Hrc.
      * apply notlt_geNonnegativeRationals in Hrc.
        apply hinhpr ; right.
        apply hinhpr ; exists (r - c / 2%NRat, c / 2%NRat) ; simpl ; repeat split.
        now rewrite minusNonnegativeRationals_plus_r.
        case (natgthorleh N N') ; intro HN.
        { apply natlthtoleh in HN.
          apply is_Dcuts_bot with (1 := Hc' _ HN).
          apply istrans_leNonnegativeRationals with r.
          now apply minusNonnegativeRationals_le.
          now apply plusNonnegativeRationals_le_r. }
        { generalize (Dcuts_lt_le_rel _ _ (pr1 (Hu _ HN)) _ (Hc' _ (isreflnatleh _))).
          apply hinhuniv ; intros [|] ; apply hinhuniv ; [intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (Hr,(Xr,Yr))].
          - apply is_Dcuts_bot with (1 := Xr).
            apply istrans_leNonnegativeRationals with r.
            now apply minusNonnegativeRationals_le.
            now apply plusNonnegativeRationals_le_r.
          - apply_pr2_in notge_ltNonnegativeRationals Yr.
            apply fromempty, Yr.
            apply istrans_leNonnegativeRationals with r.
            exact Hrc.
            now apply plusNonnegativeRationals_le_r.
          - apply is_Dcuts_bot with (1 := Xr).
            apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)%NRat).
            rewrite minusNonnegativeRationals_plus_r.
            apply istrans_leNonnegativeRationals with (r + c').
            now apply plusNonnegativeRationals_le_r.
            rewrite Hr.
            apply plusNonnegativeRationals_lecompat_l.
            now apply lt_leNonnegativeRationals.
            exact Hrc. }
        unfold Dcuts_half_val.
        now rewrite <- NQhalf_double.
    + pattern eps at 2 ;
      rewrite (Dcuts_half_double eps), <- isassoc_Dcuts_plus.
      apply Dcuts_plus_ltcompat_l.
      apply istrans_Dcuts_lt_le_rel with (Dcuts_plus (U n) (NonnegativeRationals_to_Dcuts (c / 2)%NRat)).
      now apply (pr2 (Hu _ Hn)).
      apply Dcuts_plus_lecompat_r.
      intros r Hr.
      apply is_Dcuts_bot with (1 := Hc).
      rewrite (NQhalf_double c).
      apply lt_leNonnegativeRationals, plusNonnegativeRationals_ltcompat ; apply Hr.
Qed.

(** ** Dedekind Completeness *)

Section Dcuts_of_Dcuts.

Context (E : hsubtypes Dcuts).
Context (E_bot : Π x : Dcuts, E x -> Π y : Dcuts, y <= x -> E y).
Context (E_open : Π x : Dcuts, E x -> ∃ y : Dcuts, x < y × E y).
Context (E_error: Π c : Dcuts, 0 < c -> (¬ E c) ∨ (hexists (λ P, E P × ¬ E (Dcuts_plus P c)))).

Definition Dcuts_of_Dcuts_val : NonnegativeRationals -> hProp :=
  λ r : NonnegativeRationals, ∃ X : Dcuts, (E X) × (r ∈ X).

Lemma Dcuts_of_Dcuts_bot :
  Π (x : NonnegativeRationals),
    Dcuts_of_Dcuts_val x -> Π y : NonnegativeRationals, (y <= x)%NRat -> Dcuts_of_Dcuts_val y.
Proof.
  intros r Xr n Xn.
  revert Xr ; apply hinhfun ; intros (X,(Ex,Xr)).
  exists X ; split.
  exact Ex.
  now apply is_Dcuts_bot with r.
Qed.

Lemma Dcuts_of_Dcuts_open :
  Π (x : NonnegativeRationals),
    Dcuts_of_Dcuts_val x ->
    hexists (fun y : NonnegativeRationals => dirprod (Dcuts_of_Dcuts_val y) (x < y)%NRat).
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

Lemma Dcuts_of_Dcuts_error:
  Dcuts_def_error Dcuts_of_Dcuts_val.
Proof.
  intros c Hc.
  apply ispositive_NQhalf in Hc.
  apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)) in Hc.
  generalize (E_error _ Hc).
  apply isapfun_NonnegativeRationals_to_Dcuts_aux in Hc.
  apply hinhuniv ; intros [He | ].
  - apply hinhpr ; left.
    unfold neg ; apply hinhuniv'.
    exact isapropempty.
    intros (X,(EX,Xc)).
    apply He.
    apply E_bot with (1 := EX).
    intros r Hr.
    apply is_Dcuts_bot with c.
    exact Xc.
    apply lt_leNonnegativeRationals.
    eapply istrans_lt_le_ltNonnegativeRationals.
    exact Hr.
    pattern c at 2 ;
      rewrite (NQhalf_double c).
    apply plusNonnegativeRationals_le_r.
  - apply hinhuniv ; intros (X,(EX,Hx)).
    generalize (is_Dcuts_error X _ Hc).
    apply hinhfun ; intros [Xc | ].
    + left.
      unfold neg ; apply hinhuniv'.
      exact isapropempty.
      intros (Y,(EY,Yc)).
      apply Hx.
      apply E_bot with (1 := EY).
      apply Dcuts_lt_le_rel.
      apply hinhpr.
      exists c ; split.
      2: exact Yc.
      intros H ; apply Xc.
      revert H ; apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [Xc' | Yc'] | ].
      * apply is_Dcuts_bot with (1 := Xc').
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
      * apply fromempty.
        revert Yc' ; simpl.
        change (¬ (c < c / 2)%NRat).
        apply (pr2 (notlt_geNonnegativeRationals _ _)).
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
      * intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply is_Dcuts_bot with (1 := Xc').
        apply_pr2 (plusNonnegativeRationals_lecompat_r cy).
        rewrite <- Hc'.
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals.
    + intro ; right.
      destruct t as (q,(Xq,nXq)).
      exists q ; split.
      apply hinhpr.
      now exists X ; split.
      unfold neg ; apply hinhuniv'.
      exact isapropempty.
      intros (Y,(EY,Yc)).
      apply Hx.
      apply E_bot with (1 := EY).
      intros r.
      apply hinhuniv ; intros [ | ].
      apply hinhuniv ; intros [ Xc' | Yc' ].
      * apply is_Dcuts_bot with (1 := Yc).
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_le_r.
        apply lt_leNonnegativeRationals.
        apply notge_ltNonnegativeRationals.
        intro ; apply nXq.
        now apply is_Dcuts_bot with (1 := Xc').
      * apply is_Dcuts_bot with (1 := Yc).
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_le_l.
        apply lt_leNonnegativeRationals.
        exact Yc'.
      * apply hinhuniv.
        intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply is_Dcuts_bot with (1 := Yc).
        rewrite Hc'.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        eapply istrans_leNonnegativeRationals, plusNonnegativeRationals_lecompat_l.
        apply plusNonnegativeRationals_lecompat_r.
        apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
        intro ; apply nXq.
        now apply is_Dcuts_bot with (1 := Xc').
        now apply lt_leNonnegativeRationals.
Qed.

End Dcuts_of_Dcuts.

Definition Dcuts_of_Dcuts (E : hsubtypes Dcuts) E_bot E_error : Dcuts :=
  mk_Dcuts (Dcuts_of_Dcuts_val E) (Dcuts_of_Dcuts_bot E) (Dcuts_of_Dcuts_open E) (Dcuts_of_Dcuts_error E E_bot E_error).

Section Dcuts_of_Dcuts'.

Context (E : hsubtypes NonnegativeRationals).
Context (E_bot : Dcuts_def_bot E).
Context (E_open : Dcuts_def_open E).
Context (E_error : Dcuts_def_error E).

Definition Dcuts_of_Dcuts'_val : hsubtypes Dcuts :=
  λ x : Dcuts, ∃ r : NonnegativeRationals, (¬ (r ∈ x)) × E r.

Lemma Dcuts_of_Dcuts'_bot :
  Π (x : Dcuts),
    Dcuts_of_Dcuts'_val x -> Π y : Dcuts, (y <= x) -> Dcuts_of_Dcuts'_val y.
Proof.
  intros r Xr n Xn.
  revert Xr.
  apply hinhfun.
  intros q.
  exists (pr1 q).
  split.
  intros Nq.
  apply (pr1 (pr2 q)).
  now apply Xn.
  exact (pr2 (pr2 q)).
Qed.

Lemma Dcuts_of_Dcuts'_open :
  Π (x : Dcuts),
    Dcuts_of_Dcuts'_val x ->
    hexists (fun y : Dcuts => dirprod (Dcuts_of_Dcuts'_val y) (x < y)).
Proof.
  intros r.
  apply hinhuniv.
  intros q.
  generalize (E_open _ (pr2 (pr2 q))).
  apply hinhfun.
  intros s.
  exists (NonnegativeRationals_to_Dcuts (pr1 s)).
  split.
  - apply hinhpr.
    exists (pr1 s).
    split.
    + simpl.
      now apply isirrefl_ltNonnegativeRationals.
    + exact (pr1 (pr2 s)).
  - apply hinhpr.
    exists (pr1 q).
    split.
    + exact (pr1 (pr2 q)).
    + simpl.
      exact (pr2 (pr2 s)).
Qed.

Lemma Dcuts_of_Dcuts'_error:
  Π c : Dcuts, 0 < c -> (¬ Dcuts_of_Dcuts'_val c) ∨ (hexists (λ P, Dcuts_of_Dcuts'_val P × ¬ Dcuts_of_Dcuts'_val (Dcuts_plus P c))).
Proof.
  intros C HC.
  assert (∃ c : NonnegativeRationals, c ∈ C × (0 < c)%NRat).
  { revert HC ; apply hinhuniv ; intro d.
    generalize (is_Dcuts_open _ _ (pr2 (pr2 d))).
    apply hinhfun.
    intro c.
    exists (pr1 c).
    split.
    - exact (pr1 (pr2 c)).
    - eapply istrans_le_lt_ltNonnegativeRationals, (pr2 (pr2 c)).
      now apply isnonnegative_NonnegativeRationals. }
  revert X ; apply hinhuniv ; intros (c,(Cc,Hc)).
  generalize (E_error _ Hc).
  apply hinhfun.
  intros [Ec | q].
  - left.
    unfold neg ; apply hinhuniv'.
    exact isapropempty.
    intros r.
    apply Ec.
    apply E_bot with (1 := (pr2 (pr2 r))).
    apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
    intro H.
    apply (pr1 (pr2 r)).
    now apply is_Dcuts_bot with (1 := Cc).
  - right.
    apply hinhpr.
    exists (NonnegativeRationals_to_Dcuts (pr1 q)).
    split.
    + apply hinhpr.
      exists (pr1 q).
      split.
      * simpl.
        apply isirrefl_ltNonnegativeRationals.
      * exact (pr1 (pr2 q)).
    + intro H ; apply (pr2 (pr2 q)).
      revert H.
      apply hinhuniv.
      intros r.
      apply E_bot with (1 := (pr2 (pr2 r))).
      apply notlt_geNonnegativeRationals.
      intro H.
      apply (pr1 (pr2 r)).
      destruct (isdecrel_ltNonnegativeRationals (pr1 r) c) as [H0 | H0].
      * apply hinhpr.
        left.
        apply hinhpr.
        right.
        apply is_Dcuts_bot with (1 := Cc).
        now apply lt_leNonnegativeRationals.
      * apply notlt_geNonnegativeRationals in H0.
        apply hinhpr.
        right.
        apply hinhpr.
        exists ((pr1 r - c)%NRat,c).
        simpl ; split ; [ | split].
        now apply pathsinv0, minusNonnegativeRationals_plus_r.
        apply_pr2 (plusNonnegativeRationals_ltcompat_r c).
        now rewrite minusNonnegativeRationals_plus_r.
        exact Cc.
Qed.

End Dcuts_of_Dcuts'.

Lemma Dcuts_of_Dcuts_bij :
  Π x : Dcuts, Dcuts_of_Dcuts (Dcuts_of_Dcuts'_val (pr1 x)) (Dcuts_of_Dcuts'_bot (pr1 x)) (Dcuts_of_Dcuts'_error (pr1 x) (is_Dcuts_bot x) (is_Dcuts_error x)) = x.
Proof.
  intros x.
  apply Dcuts_eq_is_eq.
  intros r.
  split.
  - apply hinhuniv.
    intros y.
    generalize (pr1 (pr2 y)).
    apply hinhuniv.
    intros q.
    apply is_Dcuts_bot with (1 := pr2 (pr2 q)).
    apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
    intro H.
    apply (pr1 (pr2 q)).
    now apply is_Dcuts_bot with (1 := pr2 (pr2 y)).
  - intros Xr.
    generalize (is_Dcuts_open _ _ Xr).
    apply hinhfun.
    intros q.
    exists (NonnegativeRationals_to_Dcuts (pr1 q)).
    split.
    + apply hinhpr.
      exists (pr1 q).
      split.
      * simpl.
        now apply isirrefl_ltNonnegativeRationals.
      * exact (pr1 (pr2 q)).
    + simpl.
      exact (pr2 (pr2 q)).
Qed.
Lemma Dcuts_of_Dcuts_bij' :
  Π E : hsubtypes Dcuts, Π (E_bot : Π x : Dcuts, E x -> Π y : Dcuts, y <= x -> E y) (E_open : Π x : Dcuts, E x -> ∃ y : Dcuts, x < y × E y),
    Dcuts_of_Dcuts'_val (Dcuts_of_Dcuts_val E) = E.
Proof.
  intros.
  apply funextfun.
  intros x.
  apply uahp.
  - apply hinhuniv.
    simpl pr1.
    intros (r,(Hr)).
    apply hinhuniv.
    intros X.
    apply E_bot with (1 := pr1 (pr2 X)).
    apply Dcuts_lt_le_rel.
    apply hinhpr.
    exists r.
    split.
    exact Hr.
    exact (pr2 (pr2 X)).
  - intros Ex.
    generalize (E_open _ Ex).
    apply hinhuniv.
    intros y.
    generalize (pr1 (pr2 y)).
    apply hinhfun.
    intros r.
    exists (pr1 r).
    split.
    exact (pr1 (pr2 r)).
    apply hinhpr.
    exists (pr1 y).
    split.
    apply (pr2 (pr2 y)).
    apply (pr2 (pr2 r)).
Qed.

Lemma isub_Dcuts_of_Dcuts (E : hsubtypes Dcuts) E_bot E_error :
  isUpperBound (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_of_Dcuts E E_bot E_error).
Proof.
  intros ;
  intros x Ex r Hr.
  apply hinhpr.
  now exists x.
Qed.
Lemma islbub_Dcuts_of_Dcuts (E : hsubtypes Dcuts) E_bot E_error :
  isSmallerThanUpperBounds (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_of_Dcuts E E_bot E_error).
Proof.
  intros.
  intros x Hx ; simpl.
  intros r ; apply hinhuniv ;
  intros (y,(Ey,Yr)).
  generalize (Hx y Ey).
  now intros H ; apply H.
Qed.
Lemma islub_Dcuts_of_Dcuts (E : hsubtypes eo_Dcuts) E_bot E_error :
  isLeastUpperBound (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_of_Dcuts E E_bot E_error).
Proof.
  split.
  exact (isub_Dcuts_of_Dcuts E E_bot E_error).
  exact (islbub_Dcuts_of_Dcuts E E_bot E_error).
Qed.



(** * Definition of non-negative real numbers *)

Global Opaque Dcuts.
Global Opaque Dcuts_le_rel
              Dcuts_lt_rel
              Dcuts_ap_rel.
Global Opaque Dcuts_zero
              Dcuts_one
              Dcuts_two
              Dcuts_plus
              Dcuts_minus
              Dcuts_mult
              Dcuts_inv
              Dcuts_max
              Dcuts_half.
Global Opaque Dcuts_lim_cauchy_seq.

Delimit Scope NR_scope with NR.
Open Scope NR_scope.

Definition NonnegativeReals : ConstructiveCommutativeDivisionRig
  := Dcuts_ConstructiveCommutativeDivisionRig.
Definition EffectivelyOrdered_NonnegativeReals : EffectivelyOrderedSet.
Proof.
  exists NonnegativeReals.
  apply (pairEffectiveOrder Dcuts_le_rel Dcuts_lt_rel iseo_Dcuts_le_lt_rel).
Defined.

(** ** Relations *)

Definition apNonnegativeReals : hrel NonnegativeReals := CCDRap.
Definition leNonnegativeReals : po NonnegativeReals := EOle (X := EffectivelyOrdered_NonnegativeReals).
Definition geNonnegativeReals : po NonnegativeReals := EOge (X := EffectivelyOrdered_NonnegativeReals).
Definition ltNonnegativeReals : StrongOrder NonnegativeReals := EOlt (X := EffectivelyOrdered_NonnegativeReals).
Definition gtNonnegativeReals : StrongOrder NonnegativeReals := EOgt (X := EffectivelyOrdered_NonnegativeReals).

Notation "x ≠ y" := (apNonnegativeReals x y) (at level 70, no associativity) : NR_scope.
Notation "x <= y" := (EOle_rel (X := EffectivelyOrdered_NonnegativeReals) x y) : NR_scope.
Notation "x >= y" := (EOge_rel (X := EffectivelyOrdered_NonnegativeReals) x y) : NR_scope.
Notation "x < y" := (EOlt_rel (X := EffectivelyOrdered_NonnegativeReals) x y) : NR_scope.
Notation "x > y" := (EOgt_rel (X := EffectivelyOrdered_NonnegativeReals) eo_Dcuts x y) : NR_scope.

(** ** Constants and Functions *)

Definition zeroNonnegativeReals : NonnegativeReals := CCDRzero.
Definition oneNonnegativeReals : NonnegativeReals := CCDRone.
Definition twoNonnegativeReals : NonnegativeReals := Dcuts_two.
Definition plusNonnegativeReals : binop NonnegativeReals := CCDRplus.
Definition multNonnegativeReals : binop NonnegativeReals := CCDRmult.

Definition NonnegativeRationals_to_NonnegativeReals (r : NonnegativeRationals) : NonnegativeReals :=
  NonnegativeRationals_to_Dcuts r.
Definition nat_to_NonnegativeReals (n : nat) : NonnegativeReals :=
  NonnegativeRationals_to_NonnegativeReals (nat_to_NonnegativeRationals n).

Notation "0" := zeroNonnegativeReals : NR_scope.
Notation "1" := oneNonnegativeReals : NR_scope.
Notation "2" := twoNonnegativeReals : NR_scope.
Notation "x + y" := (plusNonnegativeReals x y) (at level 50, left associativity) : NR_scope.
Notation "x * y" := (multNonnegativeReals x y) (at level 40, left associativity) : NR_scope.

Definition invNonnegativeReals (x : NonnegativeReals) (Hx0 : x ≠ 0) : NonnegativeReals :=
  CCDRinv x Hx0.
Definition divNonnegativeReals (x y : NonnegativeReals) (Hy0 : y ≠ 0) : NonnegativeReals :=
  x * (invNonnegativeReals y Hy0).

(** ** Special functions *)

Definition NonnegativeReals_to_hsubtypesNonnegativeRationals :
  NonnegativeReals -> (hsubtypes NonnegativeRationals) := pr1.
Definition hsubtypesNonnegativeRationals_to_NonnegativeReals
  (X : NonnegativeRationals -> hProp)
  (Xbot : Π x : NonnegativeRationals,
            X x -> Π y : NonnegativeRationals, (y <= x)%NRat -> X y)
  (Xopen : Π x : NonnegativeRationals,
             X x ->
             hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)%NRat))
  (Xtop : Dcuts_def_error X) : NonnegativeReals :=
  mk_Dcuts X Xbot Xopen Xtop.

Definition minusNonnegativeReals : binop NonnegativeReals := Dcuts_minus.
Definition halfNonnegativeReals : unop NonnegativeReals := Dcuts_half.
Definition maxNonnegativeReals : binop NonnegativeReals := Dcuts_max.

Notation "x - y" := (minusNonnegativeReals x y) (at level 50, left associativity) : NR_scope.
Notation "x / 2" := (halfNonnegativeReals x) (at level 35, no associativity) : NR_scope.

(** ** Theorems *)

(** ** Compatibility with NonnegativeRationals *)

Lemma NonnegativeRationals_to_NonnegativeReals_lt :
  Π x y : NonnegativeRationals,
    (x < y)%NRat <->
    NonnegativeRationals_to_NonnegativeReals x < NonnegativeRationals_to_NonnegativeReals y.
Proof.
  intros x y ; split.
  - intros Hxy.
    apply hinhpr.
    exists x.
    split ; simpl.
    + now apply isirrefl_ltNonnegativeRationals.
    + exact Hxy.
  - apply hinhuniv ; simpl ; intros q.
    eapply istrans_le_lt_ltNonnegativeRationals, (pr2 (pr2 q)).
    apply notlt_geNonnegativeRationals.
    exact (pr1 (pr2 q)).
Qed.

Lemma NonnegativeRationals_to_NonnegativeReals_le :
  Π x y : NonnegativeRationals,
    (x <= y)%NRat <->
    NonnegativeRationals_to_NonnegativeReals x <= NonnegativeRationals_to_NonnegativeReals y.
Proof.
  intros x y ; split.
  - intros H.
    apply Dcuts_nlt_ge.
    intro H0.
    revert H.
    apply_pr2 notge_ltNonnegativeRationals.
    apply_pr2 NonnegativeRationals_to_NonnegativeReals_lt.
    exact H0.
  - intros H.
    apply notlt_geNonnegativeRationals.
    intros H0.
    revert H.
    apply Dcuts_gt_nle.
    apply NonnegativeRationals_to_NonnegativeReals_lt.
    exact H0.
Qed.

Lemma NonnegativeRationals_to_NonnegativeReals_zero :
  NonnegativeRationals_to_NonnegativeReals 0%NRat = 0.
Proof.
  reflexivity.
Qed.
Lemma NonnegativeRationals_to_NonnegativeReals_one :
  NonnegativeRationals_to_NonnegativeReals 1%NRat = 1.
Proof.
  reflexivity.
Qed.
Lemma NonnegativeRationals_to_NonnegativeReals_plus :
  Π x y : NonnegativeRationals, NonnegativeRationals_to_NonnegativeReals (x + y)%NRat = NonnegativeRationals_to_NonnegativeReals x + NonnegativeRationals_to_NonnegativeReals y.
Proof.
  intros x y.
  apply Dcuts_eq_is_eq.
  intros r.
  split.
  - intros Hr.
    destruct (eq0orgt0NonnegativeRationals y) as [Hy | Hy].
    2: destruct (eq0orgt0NonnegativeRationals x) as [Hx | Hx].
    + rewrite Hy in Hr |- * ; clear y Hy.
      rewrite isrunit_zeroNonnegativeRationals in Hr.
      rewrite isrunit_Dcuts_plus_zero.
      exact Hr.
    + rewrite Hx in Hr |- * ; clear x Hx.
      rewrite islunit_zeroNonnegativeRationals in Hr.
      rewrite islunit_Dcuts_plus_zero.
      exact Hr.
    + assert (Hxy : (0 < x + y)%NRat).
      { apply ispositive_plusNonnegativeRationals_r.
        exact Hy. }
      apply hinhpr ; right.
      apply hinhpr.
      exists ((r * (x / (x + y)))%NRat,(r * (y / (x + y)))%NRat).
      simpl.
      split ; [ | split].
      * unfold divNonnegativeRationals.
        rewrite <- isldistr_mult_plusNonnegativeRationals, <- isrdistr_mult_plusNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
        reflexivity.
        exact Hxy.
      * unfold divNonnegativeRationals.
        rewrite <- isassoc_multNonnegativeRationals, (iscomm_multNonnegativeRationals _ x), isassoc_multNonnegativeRationals.
        pattern x at 3 ;
          rewrite <- (isrunit_oneNonnegativeRationals x).
        apply multNonnegativeRationals_ltcompat_l.
        exact Hx.
        rewrite <- (isrinv_NonnegativeRationals (x + y)%NRat).
        apply multNonnegativeRationals_ltcompat_r.
        apply ispositive_invNonnegativeRationals.
        exact Hxy.
        exact Hr.
        exact Hxy.
      * unfold divNonnegativeRationals.
        rewrite <- isassoc_multNonnegativeRationals, (iscomm_multNonnegativeRationals _ y), isassoc_multNonnegativeRationals.
        pattern y at 3 ;
          rewrite <- (isrunit_oneNonnegativeRationals y).
        apply multNonnegativeRationals_ltcompat_l.
        exact Hy.
        rewrite <- (isrinv_NonnegativeRationals (x + y)%NRat).
        apply multNonnegativeRationals_ltcompat_r.
        apply ispositive_invNonnegativeRationals.
        exact Hxy.
        exact Hr.
        exact Hxy.
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [Hrx | Hry] | intros ((rx,ry)) ; simpl ; intros (->,(Hrx,Hry))] ; simpl.
    + eapply istrans_lt_le_ltNonnegativeRationals, plusNonnegativeRationals_le_r.
      exact Hrx.
    + eapply istrans_lt_le_ltNonnegativeRationals, plusNonnegativeRationals_le_l.
      exact Hry.
    + apply plusNonnegativeRationals_ltcompat.
      exact Hrx.
      exact Hry.
Qed.

Lemma NonnegativeRationals_to_NonnegativeReals_minus :
  Π x y : NonnegativeRationals, NonnegativeRationals_to_NonnegativeReals (x - y)%NRat = NonnegativeRationals_to_NonnegativeReals x - NonnegativeRationals_to_NonnegativeReals y.
Proof.
  intros x y.
  destruct (isdecrel_leNonnegativeRationals x y) as [Hxy | Hxy].
  - rewrite minusNonnegativeRationals_eq_zero, Dcuts_minus_eq_zero.
    reflexivity.
    apply NonnegativeRationals_to_NonnegativeReals_le.
    exact Hxy.
    exact Hxy.
  - apply Dcuts_minus_correct_r.
    rewrite <- NonnegativeRationals_to_NonnegativeReals_plus, minusNonnegativeRationals_plus_r.
    reflexivity.
    apply lt_leNonnegativeRationals.
    apply notge_ltNonnegativeRationals.
    exact Hxy.
Qed.
Lemma NonnegativeRationals_to_NonnegativeReals_mult :
  Π x y : NonnegativeRationals, NonnegativeRationals_to_NonnegativeReals (x * y)%NRat = NonnegativeRationals_to_NonnegativeReals x * NonnegativeRationals_to_NonnegativeReals y.
Proof.
  intros x y.
  destruct (eq0orgt0NonnegativeRationals x) as [-> | Hx].
  - rewrite islabsorb_zero_multNonnegativeRationals, islabsorb_Dcuts_mult_zero.
    reflexivity.
  - rewrite <- (Dcuts_NQmult_mult _ _ Hx).
    apply Dcuts_eq_is_eq.
    intros r.
    split.
    + simpl ; intros Hr ; apply hinhpr.
      exists (r / x)%NRat.
      split.
      * apply pathsinv0, multdivNonnegativeRationals.
        exact Hx.
      * rewrite <- (isrunit_oneNonnegativeRationals y), <- (isrinv_NonnegativeRationals x), <- isassoc_multNonnegativeRationals.
        apply multNonnegativeRationals_ltcompat_r.
        apply ispositive_invNonnegativeRationals.
        exact Hx.
        rewrite iscomm_multNonnegativeRationals.
        exact Hr.
        exact Hx.
    + apply hinhuniv.
      simpl.
      intros ry.
      rewrite (pr1 (pr2 ry)).
      apply multNonnegativeRationals_ltcompat_l.
      exact Hx.
      exact (pr2 (pr2 ry)).
Qed.

Lemma NonnegativeRationals_to_NonnegativeReals_nattorig :
  Π n : nat, NonnegativeRationals_to_NonnegativeReals (nattorig n) = nattorig n.
Proof.
  induction n.
  - reflexivity.
  - rewrite !nattorigS.
    rewrite NonnegativeRationals_to_NonnegativeReals_plus, IHn.
    reflexivity.
Qed.

Lemma nat_to_NonnegativeReals_O :
  nat_to_NonnegativeReals O = 0.
Proof.
  unfold nat_to_NonnegativeReals.
  rewrite nat_to_NonnegativeRationals_O.
  reflexivity.
Qed.
Lemma nat_to_NonnegativeReals_Sn :
  Π n : nat, nat_to_NonnegativeReals (S n) = nat_to_NonnegativeReals n + 1.
Proof.
  intros n.
  unfold nat_to_NonnegativeReals.
  rewrite nat_to_NonnegativeRationals_Sn.
  rewrite NonnegativeRationals_to_NonnegativeReals_plus.
  reflexivity.
Qed.

(** Order, apartness, and equality *)

Definition istrans_leNonnegativeReals :
  Π x y z : NonnegativeReals, x <= y -> y <= z -> x <= z
  := istrans_EOle (X := EffectivelyOrdered_NonnegativeReals).
Definition isrefl_leNonnegativeReals :
  Π x : NonnegativeReals, x <= x
  := isrefl_EOle (X := EffectivelyOrdered_NonnegativeReals).
Lemma isantisymm_leNonnegativeReals :
  Π x y : NonnegativeReals, x <= y × y <= x <-> x = y.
Proof.
  intros x y ; split.
  - intros (Hle,Hge).
    apply Dcuts_le_ge_eq.
    now apply Hle.
    now apply Hge.
  -  intros ->.
     split ; apply isrefl_leNonnegativeReals.
Qed.

Definition istrans_ltNonnegativeReals :
  Π x y z : NonnegativeReals, x < y -> y < z -> x < z
  := istrans_EOlt (X := EffectivelyOrdered_NonnegativeReals).
Definition iscotrans_ltNonnegativeReals :
  Π x y z : NonnegativeReals, x < z -> x < y ∨ y < z
  := iscotrans_Dcuts_lt_rel.
Definition isirrefl_ltNonnegativeReals :
  Π x : NonnegativeReals, ¬ (x < x)
  := isirrefl_EOlt (X := EffectivelyOrdered_NonnegativeReals).

Definition istrans_lt_le_ltNonnegativeReals :
  Π x y z : NonnegativeReals, x < y -> y <= z -> x < z
  := istrans_EOlt_le (X := EffectivelyOrdered_NonnegativeReals).
Definition istrans_le_lt_ltNonnegativeReals :
  Π x y z : NonnegativeReals, x <= y -> y < z -> x < z
  := istrans_EOle_lt (X := EffectivelyOrdered_NonnegativeReals).

Lemma lt_leNonnegativeReals :
  Π x y : NonnegativeReals, x < y -> x <= y.
Proof.
  exact Dcuts_lt_le_rel.
Qed.
Lemma notlt_leNonnegativeReals :
  Π x y : NonnegativeReals, ¬ (x < y) <-> (y <= x).
Proof.
  exact Dcuts_nlt_ge.
Qed.

Lemma isnonnegative_NonnegativeReals :
  Π x : NonnegativeReals, 0 <= x.
Proof.
  intros x.
  now apply Dcuts_ge_0.
Qed.
Lemma isnonnegative_NonnegativeReals' :
  Π x : NonnegativeReals, ¬ (x < 0).
Proof.
  intros x.
  now apply Dcuts_notlt_0.
Qed.
Lemma le0_NonnegativeReals :
  Π x : NonnegativeReals, (x <= 0) <-> (x = 0).
Proof.
  intros x ; split ; intros Hx.
  apply isantisymm_leNonnegativeReals.
  - split.
    exact Hx.
    apply isnonnegative_NonnegativeReals.
  - rewrite Hx.
    apply isrefl_leNonnegativeReals.
Qed.

Lemma ap_ltNonnegativeReals :
  Π x y : NonnegativeReals, x ≠ y <-> (x < y) ⨿  (y < x).
Proof.
  now intros x y ; split.
Qed.
Definition isirrefl_apNonnegativeReals :
  Π x : NonnegativeReals, ¬ (x ≠ x)
  := isirrefl_Dcuts_ap_rel.
Definition issymm_apNonnegativeReals :
  Π x y : NonnegativeReals, x ≠ y -> y ≠ x
  := issymm_Dcuts_ap_rel.
Definition iscotrans_apNonnegativeReals :
  Π x y z : NonnegativeReals, x ≠ z -> x ≠ y ∨ y ≠ z
  := iscotrans_Dcuts_ap_rel.
Lemma istight_apNonnegativeReals:
  Π x y : NonnegativeReals, (¬ (x ≠ y)) <-> (x = y).
Proof.
  intros x y.
  split.
  - now apply istight_Dcuts_ap_rel.
  - intros ->.
    now apply isirrefl_Dcuts_ap_rel.
Qed.

Lemma ispositive_apNonnegativeReals :
  Π x : NonnegativeReals, x ≠ 0 <-> 0 < x.
Proof.
  intros X ; split.
  - intros [ | Hlt ].
    apply hinhuniv ; intros (x,(_,Hx)).
    now apply Dcuts_zero_empty in Hx.
    exact Hlt.
  - intros Hx.
    now right.
Qed.

Definition isnonzeroNonnegativeReals: 1 ≠ 0
  := isnonzeroCCDR (X := NonnegativeReals).

Lemma ispositive_oneNonnegativeReals: 0 < 1.
Proof.
  apply ispositive_apNonnegativeReals.
  exact isnonzeroNonnegativeReals.
Qed.

(** addition *)

Definition ap_plusNonnegativeReals:
  Π x x' y y' : NonnegativeReals,
    x + y ≠ x' + y' -> x ≠ x' ∨ y ≠ y'
  := apCCDRplus (X := NonnegativeReals).

Definition islunit_zero_plusNonnegativeReals:
  Π x : NonnegativeReals, 0 + x = x
  := islunit_CCDRzero_CCDRplus (X := NonnegativeReals).
Definition isrunit_zero_plusNonnegativeReals:
  Π x : NonnegativeReals, x + 0 = x
  := isrunit_CCDRzero_CCDRplus (X := NonnegativeReals).
Definition isassoc_plusNonnegativeReals:
  Π x y z : NonnegativeReals, x + y + z = x + (y + z)
  := isassoc_CCDRplus (X := NonnegativeReals).
Definition iscomm_plusNonnegativeReals:
  Π x y : NonnegativeReals, x + y = y + x
  := iscomm_CCDRplus (X := NonnegativeReals).

Definition plusNonnegativeReals_ltcompat_l :
  Π x y z: NonnegativeReals, (y < z) <-> (y + x < z + x)
  := Dcuts_plus_ltcompat_l.
Definition plusNonnegativeReals_ltcompat_r :
  Π x y z: NonnegativeReals, (y < z) <-> (x + y < x + z)
  := Dcuts_plus_ltcompat_r.

Lemma plusNonnegativeReals_ltcompat :
  Π x y z t : NonnegativeReals, x < y -> z < t -> x + z < y + t.
Proof.
  intros x y z t Hxy Hzt.
  eapply istrans_ltNonnegativeReals, plusNonnegativeReals_ltcompat_l.
  now apply plusNonnegativeReals_ltcompat_r.
  exact Hxy.
Qed.
Lemma plusNonnegativeReals_lt_l:
  Π x y : NonnegativeReals, 0 < x <-> y < x + y.
Proof.
  intros x y.
  pattern y at 1.
  rewrite <- (islunit_zero_plusNonnegativeReals y).
  now apply plusNonnegativeReals_ltcompat_l.
Qed.
Lemma plusNonnegativeReals_lt_r:
  Π x y : NonnegativeReals, 0 < y <-> x < x + y.
Proof.
  intros x y.
  pattern x at 1.
  rewrite <- (isrunit_zero_plusNonnegativeReals x).
  now apply plusNonnegativeReals_ltcompat_r.
Qed.

Definition plusNonnegativeReals_lecompat_l :
  Π x y z: NonnegativeReals, (y <= z) <-> (y + x <= z + x)
  := Dcuts_plus_lecompat_l.
Definition plusNonnegativeReals_lecompat_r :
  Π x y z: NonnegativeReals, (y <= z) <-> (x + y <= x + z)
  := Dcuts_plus_lecompat_r.
Lemma plusNonnegativeReals_lecompat :
  Π x y x' y' : NonnegativeReals,
    x <= y -> x' <= y' -> x + x' <= y + y'.
Proof.
  intros x y x' y' H H'.
  refine (istrans_leNonnegativeReals _ _ _ _ _).
  apply plusNonnegativeReals_lecompat_l.
  apply H.
  apply plusNonnegativeReals_lecompat_r.
  exact H'.
Qed.

Lemma plusNonnegativeReals_le_l :
  Π (x y : NonnegativeReals), x <= x + y.
Proof.
  exact Dcuts_plus_le_l.
Qed.
Lemma plusNonnegativeReals_le_r :
  Π (x y : NonnegativeReals), y <= x + y.
Proof.
  exact Dcuts_plus_le_r.
Qed.

Lemma plusNonnegativeReals_le_ltcompat :
  Π x y z t : NonnegativeReals,
    x <= y -> z < t -> x + z < y + t.
Proof.
  intros x y z t Hxy Hzt.
  eapply istrans_le_lt_ltNonnegativeReals, plusNonnegativeReals_ltcompat_r, Hzt.
  now apply plusNonnegativeReals_lecompat_l.
Qed.

Lemma plusNonnegativeReals_eqcompat_l :
  Π x y z: NonnegativeReals, (y + x = z + x) <-> (y = z).
Proof.
  intros x y z ; split.
  - intro H ;
    apply isantisymm_leNonnegativeReals ; split.
    + apply_pr2 (plusNonnegativeReals_lecompat_l x).
      rewrite H ; refine (isrefl_leNonnegativeReals _).
    + apply_pr2 (plusNonnegativeReals_lecompat_l x).
      rewrite H ; refine (isrefl_leNonnegativeReals _).
  - now intros ->.
Qed.
Lemma plusNonnegativeReals_eqcompat_r :
  Π x y z: NonnegativeReals, (x + y = x + z) <-> (y = z).
Proof.
  intros x y z.
  rewrite ! (iscomm_plusNonnegativeReals x).
  now apply plusNonnegativeReals_eqcompat_l.
Qed.

Lemma plusNonnegativeReals_apcompat_l :
  Π x y z: NonnegativeReals, (y ≠ z) <-> (y + x ≠ z + x).
Proof.
  intros a b c.
  split.
  - intro H.
    apply ap_ltNonnegativeReals.
    apply_pr2_in ap_ltNonnegativeReals H.
    destruct H as [H | H].
    + left ;
      now apply plusNonnegativeReals_ltcompat_l.
    + right ;
      now apply plusNonnegativeReals_ltcompat_l.
  - now apply islapbinop_Dcuts_plus.
Qed.
Lemma plusNonnegativeReals_apcompat_r :
  Π x y z: NonnegativeReals, (y ≠ z) <-> (x + y ≠ x + z).
Proof.
  intros x y z.
  rewrite ! (iscomm_plusNonnegativeReals x).
  now apply plusNonnegativeReals_apcompat_l.
Qed.

(** Subtraction *)

Definition minusNonnegativeReals_plus_r :
  Π x y z : NonnegativeReals, z <= y -> x = y - z -> y = x + z
  := Dcuts_minus_plus_r.
Definition minusNonnegativeReals_eq_zero :
  Π x y : NonnegativeReals, x <= y -> x - y = 0
  := Dcuts_minus_eq_zero.
Definition minusNonnegativeReals_correct_r :
  Π x y z : NonnegativeReals, x = y + z -> y = x - z
  := Dcuts_minus_correct_r.
Definition minusNonnegativeReals_correct_l :
  Π x y z : NonnegativeReals, x = y + z -> z = x - y
  := Dcuts_minus_correct_l.
Definition ispositive_minusNonnegativeReals :
  Π x y : NonnegativeReals, (y < x) <-> (0 < x - y)
  := ispositive_Dcuts_minus.
Definition minusNonnegativeReals_le :
  Π x y : NonnegativeReals, x - y <= x
  := Dcuts_minus_le.

(** Multiplication *)

Definition ap_multNonnegativeReals:
  Π x x' y y' : NonnegativeReals,
    x * y ≠ x' * y' -> x ≠ x' ∨ y ≠ y'
  := apCCDRmult (X := NonnegativeReals).

Definition islunit_one_multNonnegativeReals:
  Π x : NonnegativeReals, 1 * x = x
  := islunit_CCDRone_CCDRmult (X := NonnegativeReals).
Definition isrunit_one_multNonnegativeReals:
  Π x : NonnegativeReals, x * 1 = x
  := isrunit_CCDRone_CCDRmult (X := NonnegativeReals).
Definition isassoc_multNonnegativeReals:
  Π x y z : NonnegativeReals, x * y * z = x * (y * z)
  := isassoc_CCDRmult (X := NonnegativeReals).
Definition iscomm_multNonnegativeReals:
  Π x y : NonnegativeReals, x * y = y * x
  := iscomm_CCDRmult (X := NonnegativeReals).
Definition islabsorb_zero_multNonnegativeReals:
  Π x : NonnegativeReals, 0 * x = 0
  := islabsorb_CCDRzero_CCDRmult (X := NonnegativeReals).
Definition israbsorb_zero_multNonnegativeReals:
  Π x : NonnegativeReals, x * 0 = 0
  := israbsorb_CCDRzero_CCDRmult (X := NonnegativeReals).

Definition multNonnegativeReals_ltcompat_l :
  Π x y z: NonnegativeReals, (0 < x) -> (y < z) -> (y * x < z * x)
  := Dcuts_mult_ltcompat_l.
Definition multNonnegativeReals_ltcompat_l' :
  Π x y z: NonnegativeReals, (y * x < z * x) -> (y < z)
  := Dcuts_mult_ltcompat_l'.
Definition multNonnegativeReals_lecompat_l :
  Π x y z: NonnegativeReals, (0 < x) -> (y * x <= z * x) -> (y <= z)
  := Dcuts_mult_lecompat_l.
Definition multNonnegativeReals_lecompat_l' :
  Π x y z: NonnegativeReals, (y <= z) -> (y * x <= z * x)
  := Dcuts_mult_lecompat_l'.

Definition multNonnegativeReals_ltcompat_r :
  Π x y z: NonnegativeReals, (0 < x) -> (y < z) -> (x * y < x * z)
  := Dcuts_mult_ltcompat_r.
Definition multNonnegativeReals_ltcompat_r' :
  Π x y z: NonnegativeReals, (x * y < x *  z) -> (y < z)
  := Dcuts_mult_ltcompat_r'.
Definition multNonnegativeReals_lecompat_r :
  Π x y z: NonnegativeReals, (0 < x) -> (x * y <= x * z) -> (y <= z)
  := Dcuts_mult_lecompat_r.
Definition multNonnegativeReals_lecompat_r' :
  Π x y z: NonnegativeReals, (y <= z) -> (x * y <= x * z)
  := Dcuts_mult_lecompat_r'.

(** Multiplicative Inverse *)

Definition islinv_invNonnegativeReals:
  Π (x : NonnegativeReals) (Hx0 : x ≠ 0), invNonnegativeReals x Hx0 * x = 1
  := islinv_CCDRinv (X := NonnegativeReals).
Definition isrinv_invNonnegativeReals:
  Π (x : NonnegativeReals) (Hx0 : x ≠ 0), x * invNonnegativeReals x Hx0 = 1
  := isrinv_CCDRinv (X := NonnegativeReals).

Definition isldistr_plus_multNonnegativeReals:
  Π x y z : NonnegativeReals, z * (x + y) = z * x + z * y
  := isldistr_CCDRplus_CCDRmult (X := NonnegativeReals).
Definition isrdistr_plus_multNonnegativeReals:
  Π x y z : NonnegativeReals, (x + y) * z = x * z + y * z
  := isrdistr_CCDRplus_CCDRmult (X := NonnegativeReals).

(** maximum *)

Lemma iscomm_maxNonnegativeReals :
  Π x y : NonnegativeReals,
    maxNonnegativeReals x y = maxNonnegativeReals y x.
Proof.
  exact iscomm_Dcuts_max.
Qed.
Lemma isassoc_maxNonnegativeReals :
  Π x y z : NonnegativeReals,
    maxNonnegativeReals (maxNonnegativeReals x y) z =
    maxNonnegativeReals x (maxNonnegativeReals y z).
Proof.
  exact isassoc_Dcuts_max.
Qed.

Lemma isldistr_max_plusNonnegativeReals :
  Π x y z : NonnegativeReals,
    z + maxNonnegativeReals x y = maxNonnegativeReals (z + x) (z + y).
Proof.
  exact isldistr_Dcuts_max_plus.
Qed.
Lemma isrdistr_max_plusNonnegativeReals :
  Π x y z : NonnegativeReals,
    maxNonnegativeReals x y + z = maxNonnegativeReals (x + z) (y + z).
Proof.
  intros x y z.
  rewrite !(iscomm_plusNonnegativeReals _ z).
  now apply isldistr_max_plusNonnegativeReals.
Qed.

Lemma isldistr_max_multNonnegativeReals :
  Π x y z : NonnegativeReals,
    z * maxNonnegativeReals x y = maxNonnegativeReals (z * x) (z * y).
Proof.
  exact isldistr_Dcuts_max_mult.
Qed.
Lemma isrdistr_max_multNonnegativeReals :
  Π x y z : NonnegativeReals,
    maxNonnegativeReals x y * z = maxNonnegativeReals (x * z) (y * z).
Proof.
  intros x y z.
  rewrite !(iscomm_multNonnegativeReals _ z).
  now apply isldistr_max_multNonnegativeReals.
Qed.

Lemma maxNonnegativeReals_carac_l :
  Π x y : NonnegativeReals,
    y <= x -> maxNonnegativeReals x y = x.
Proof.
  exact Dcuts_max_carac_l.
Qed.
Lemma maxNonnegativeReals_carac_r :
  Π x y : NonnegativeReals,
    x <= y -> maxNonnegativeReals x y = y.
Proof.
  exact Dcuts_max_carac_r.
Qed.

Lemma maxNonnegativeReals_le_l :
  Π x y : NonnegativeReals,
    x <= maxNonnegativeReals x y.
Proof.
  exact Dcuts_max_le_l.
Qed.
Lemma maxNonnegativeReals_le_r :
  Π x y : NonnegativeReals,
    y <= maxNonnegativeReals x y.
Proof.
  exact Dcuts_max_le_r.
Qed.

Lemma maxNonnegativeReals_lt :
  Π x y z : NonnegativeReals,
    x < z -> y < z
    -> maxNonnegativeReals x y < z.
Proof.
  exact Dcuts_max_lt.
Qed.
Lemma maxNonnegativeReals_le :
  Π x y z : NonnegativeReals,
    x <= z -> y <= z
    -> maxNonnegativeReals x y <= z.
Proof.
  exact Dcuts_max_le.
Qed.

Lemma maxNonnegativeReals_minus_plus:
  Π x y : NonnegativeReals,
    maxNonnegativeReals x y = (x - y) + y.
Proof.
  intros x y.
  apply pathsinv0.
  now apply Dcuts_minus_plus_max.
Qed.

Lemma isldistr_minus_multNonnegativeReals :
  Π x y z : NonnegativeReals, z * (x - y) = z * x - z * y.
Proof.
  intros x y z.
  apply plusNonnegativeReals_eqcompat_l with (Dcuts_mult z y).
  rewrite <- isldistr_plus_multNonnegativeReals, <- !maxNonnegativeReals_minus_plus.
  apply isldistr_max_multNonnegativeReals.
Qed.
Lemma isrdistr_minus_multNonnegativeReals :
   Π x y z : NonnegativeReals, (x - y) * z = x * z - y * z.
Proof.
  intros x y z.
  rewrite !(iscomm_multNonnegativeReals _ z).
  now apply isldistr_minus_multNonnegativeReals.
Qed.

Lemma isassoc_minusNonnegativeReals :
  Π x y z : NonnegativeReals,
    (x - y) - z = x - (y + z).
Proof.
  intros x y z.
  apply plusNonnegativeReals_eqcompat_l with (y + z).
  rewrite <- maxNonnegativeReals_minus_plus.
  rewrite (iscomm_plusNonnegativeReals y).
  rewrite <- isassoc_plusNonnegativeReals.
  rewrite <- maxNonnegativeReals_minus_plus.
  rewrite isrdistr_max_plusNonnegativeReals.
  rewrite <- maxNonnegativeReals_minus_plus.
  rewrite isassoc_maxNonnegativeReals.
  apply maponpaths.
  apply maxNonnegativeReals_carac_r.
  now apply plusNonnegativeReals_le_r.
Qed.
Lemma iscomm_minusNonnegativeReals :
  Π x y z : NonnegativeReals,
    x - y - z = x - z - y.
Proof.
  intros x y z.
  rewrite !isassoc_minusNonnegativeReals.
  apply maponpaths.
  now apply iscomm_plusNonnegativeReals.
Qed.

Lemma max_plusNonnegativeReals :
  Π x y : NonnegativeReals,
    (0 < x -> y = 0) ->
    maxNonnegativeReals x y = x + y.
Proof.
  exact Dcuts_max_plus.
Qed.

(** half of a non-negative real numbers *)

Lemma double_halfNonnegativeReals :
  Π x : NonnegativeReals, x = (x / 2) + (x / 2).
Proof.
  exact Dcuts_half_double.
Qed.
Lemma isdistr_plus_halfNonnegativeReals:
  Π x y : NonnegativeReals,
    (x + y) / 2 = (x / 2) + (y / 2).
Proof.
  exact isdistr_Dcuts_half_plus.
Qed.
Lemma ispositive_halfNonnegativeReals:
  Π x : NonnegativeReals,
    (0 < x) <-> (0 < x / 2).
Proof.
  exact ispositive_Dcuts_half.
Qed.

(** ** NonnegativeRationals is dense in NonnegativeReals *)

Lemma NonnegativeReals_dense :
  Π x y : NonnegativeReals, x < y -> ∃ r : NonnegativeRationals, x < NonnegativeRationals_to_NonnegativeReals r × NonnegativeRationals_to_NonnegativeReals r < y.
Proof.
  intros x y.
  apply hinhuniv ; intros q.
  generalize (is_Dcuts_open y (pr1 q) (pr2 (pr2 q))).
  apply hinhfun ; intros r.
  exists (pr1 r) ; split ; apply hinhpr.
  - exists (pr1 q) ; split.
    + exact (pr1 (pr2 q)).
    + exact (pr2 (pr2 r)).
  - exists (pr1 r) ; split.
    + exact (isirrefl_ltNonnegativeRationals _).
    + exact (pr1 (pr2 r)).
Qed.

(** ** Archimedean property *)

Lemma NonnegativeReals_Archimedean :
  isarchrig gtNonnegativeReals.
Proof.
  set (H := isarchNonnegativeRationals).
  repeat split.
  - intros y1 y2 Hy.
    generalize (NonnegativeReals_dense _ _ Hy).
    apply hinhuniv ; clear Hy.
    intros (r2,(Hr2,Hy)).
    generalize (NonnegativeReals_dense _ _ Hy).
    apply hinhuniv ; clear Hy.
    intros (r1,(Hr,Hr1)).
    generalize (isarchrig_1 _ H _ _ (pr2 (NonnegativeRationals_to_NonnegativeReals_lt r2 r1) Hr)).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    eapply istrans_le_lt_ltNonnegativeReals, istrans_lt_le_ltNonnegativeReals.
    2: apply NonnegativeRationals_to_NonnegativeReals_lt, Hn.
    rewrite NonnegativeRationals_to_NonnegativeReals_plus, NonnegativeRationals_to_NonnegativeReals_mult,  NonnegativeRationals_to_NonnegativeReals_nattorig.
    apply plusNonnegativeReals_lecompat_r, multNonnegativeReals_lecompat_r'.
    apply lt_leNonnegativeReals, Hr2.
    rewrite NonnegativeRationals_to_NonnegativeReals_mult, NonnegativeRationals_to_NonnegativeReals_nattorig.
    apply multNonnegativeReals_lecompat_r'.
    apply lt_leNonnegativeReals, Hr1.
  - intros x.
    generalize (Dcuts_def_error_finite _ (is_Dcuts_error x)).
    apply hinhuniv ; intros (r,Hr).
    generalize (isarchrig_2 _ H r).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    apply istrans_le_lt_ltNonnegativeReals with (NonnegativeRationals_to_NonnegativeReals r).
    apply NonnegativeRationals_to_Dcuts_notin_le.
    exact Hr.
    rewrite <- NonnegativeRationals_to_NonnegativeReals_nattorig.
    apply NonnegativeRationals_to_NonnegativeReals_lt.
    exact Hn.
  - intros x.
    apply hinhpr.
    exists 1%nat.
    apply istrans_lt_le_ltNonnegativeReals with 1.
    apply ispositive_oneNonnegativeReals.
    apply plusNonnegativeReals_le_l.
Qed.

(** ** Completeness *)

Definition Cauchy_seq (u : nat -> NonnegativeReals) : hProp
  := hProppair (Π eps : NonnegativeReals,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            Π n m : nat, N ≤ n -> N ≤ m -> u n < u m + eps × u m < u n + eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).
Definition is_lim_seq (u : nat -> NonnegativeReals) (l : NonnegativeReals) : hProp
  := hProppair (Π eps : NonnegativeReals,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            Π n : nat, N ≤ n -> u n < l + eps × l < u n + eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).

Definition Cauchy_lim_seq (u : nat -> NonnegativeReals) (Cu : Cauchy_seq u) : NonnegativeReals
  := (Dcuts_lim_cauchy_seq u Cu).
Definition Cauchy_seq_impl_ex_lim_seq (u : nat -> NonnegativeReals) (Cu : Cauchy_seq u) : is_lim_seq u (Cauchy_lim_seq u Cu)
  := (Dcuts_Cauchy_seq_impl_ex_lim_seq u Cu).

(** Additionals theorems and definitions about limits *)

Lemma is_lim_seq_unique_aux (u : nat -> NonnegativeReals) (l l' : NonnegativeReals) :
  is_lim_seq u l -> is_lim_seq u l' -> l < l' -> empty.
Proof.
  intros u l l' Hl Hl' Hlt.
  assert (Hlt0 : 0 < l' - l).
  { now apply ispositive_minusNonnegativeReals. }
  assert (Hlt0' : 0 < (l' - l) / 2).
  { now apply ispositive_Dcuts_half. }
  generalize (Hl _ Hlt0') (Hl' _ Hlt0') ; clear Hl Hl'.
  apply (hinhuniv2 (P := hProppair _ isapropempty)).
  intros (N,Hn) (M,Hm).
  specialize (Hn (max N M) (max_le_l _ _)).
  specialize (Hm (max N M) (max_le_r _ _)).
  apply (isirrefl_Dcuts_lt_rel ((l + l') / 2)).
  apply istrans_Dcuts_lt_rel with (u (max N M)).
  - apply_pr2 (plusNonnegativeReals_ltcompat_l ((l' - l) / 2)).
    rewrite <- isdistr_Dcuts_half_plus.
    rewrite (iscomm_plusNonnegativeReals l), isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals l).
    rewrite <- (minusNonnegativeReals_plus_r (l' - l) l' l), isdistr_Dcuts_half_plus, <- Dcuts_half_double.
    exact (pr2 Hm).
    now apply Dcuts_lt_le_rel.
    reflexivity.
  - rewrite (minusNonnegativeReals_plus_r (l' - l) l' l), (iscomm_plusNonnegativeReals _ l), <- isassoc_plusNonnegativeReals, !isdistr_Dcuts_half_plus, <- Dcuts_half_double.
    exact (pr1 Hn).
    now apply Dcuts_lt_le_rel.
    reflexivity.
Qed.
Lemma is_lim_seq_unique (u : nat -> NonnegativeReals) (l l' : NonnegativeReals) :
  is_lim_seq u l -> is_lim_seq u l' -> l = l'.
Proof.
  intros u l l' Hl Hl'.
  apply istight_apNonnegativeReals.
  intros [ | ].
  - now apply (is_lim_seq_unique_aux u).
  - now apply (is_lim_seq_unique_aux u).
Qed.
Lemma isaprop_ex_lim_seq :
  Π u : nat -> NonnegativeReals, isaprop (Σ l : NonnegativeReals, is_lim_seq u l).
Proof.
  intros u l l'.
  apply (iscontrweqf (X := (pr1 l = pr1 l'))).
  now apply invweq, total2_paths_hProp_equiv.
  rewrite (is_lim_seq_unique _ _ _ (pr2 l) (pr2 l')).
  apply iscontrloopsifisaset.
  apply pr2.
Qed.
Definition ex_lim_seq  (u : nat -> NonnegativeReals) : hProp
  := hProppair (Σ l : NonnegativeReals, is_lim_seq u l) (isaprop_ex_lim_seq u).
Definition Lim_seq (u : nat -> NonnegativeReals) (Lu : ex_lim_seq u) : NonnegativeReals
  := pr1 Lu.

(* End of the file NonnegativeReals.v *)
