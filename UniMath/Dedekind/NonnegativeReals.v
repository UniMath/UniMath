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
  ∀ x : NonnegativeRationals, X x ->
    ∀ y : NonnegativeRationals, y <= x -> X y.
Definition Dcuts_def_open (X : hsubtypes NonnegativeRationals) : UU :=
  ∀ x : NonnegativeRationals, X x ->
    hexists (fun y : NonnegativeRationals => (X y) × (x < y)).
Definition Dcuts_def_finite (X : hsubtypes NonnegativeRationals) : hProp :=
  hexists (fun ub : NonnegativeRationals => ¬ (X ub)).
Definition Dcuts_def_error (X : hsubtypes NonnegativeRationals) : UU :=
  ∀ r, 0 < r -> (¬ (X r)) ∨ (hexists (λ q, (X q) × (¬ (X (q + r))))).
Definition Dcuts_def_error' (X : hsubtypes NonnegativeRationals) (k : NonnegativeRationals) : UU :=
  ∀ r, 0 < r -> r <= k -> (¬ (X r)) ∨ (hexists (λ q, (0 < q) × (X q) × (¬ (X (q + r))))).

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
      now apply plusNonnegativeRationals_lecompat_r ; apply lt_leNonnegativeRationals.
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
  - revert Hx ; apply hinhfun ; intros (x,(_,Hx)).
    exists (x + 1) ; exact Hx.
Qed.

Lemma Dcuts_def_error_not_empty (X : hsubtypes NonnegativeRationals) :
  X 0 -> Dcuts_def_error X ->
  ∀ c : NonnegativeRationals,
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
  ∀ X : Dcuts_set, ∀ r : NonnegativeRationals,
    neg (r ∈ X) -> ∀ n : NonnegativeRationals, n ∈ X -> n < r.
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
          hProppair (∀ x : NonnegativeRationals, x ∈ X -> x ∈ Y)
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
  assert (Hr0 : 0%NRat < r' - r) by (now apply minusNonnegativeRationals_gt0).
  generalize (is_Dcuts_error y _ Hr0) ; apply hinhuniv ; intros [Yq | Yq].
  - apply Utilities.squash_element ;
    right ; apply Utilities.squash_element.
    exists r' ; split.
    + intro H0 ; apply Yq.
      apply is_Dcuts_bot with r'.
      exact H0.
      now apply minusNonnegativeRationals_le.
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
        apply (plusNonnegativeRationals_ltcompat_r r) in Hdec ;
          rewrite isassoc_plusNonnegativeRationals, minusNonegativeRationals_plus_r, iscomm_plusNonnegativeRationals in Hdec.
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
  ∀ x y : Dcuts_set, Dcuts_lt_rel x y -> Dcuts_le_rel x y.
Proof.
  intros x y ; apply hinhuniv ; intros (r,(Xr,Yr)).
  intros n Xn.
  apply is_Dcuts_bot with r.
  exact Yr.
  apply lt_leNonnegativeRationals.
  now apply Dcuts_finite with x.
Qed.

Lemma Dcuts_le_ngt_rel :
  ∀ x y : Dcuts_set, ¬ Dcuts_lt_rel x y <-> Dcuts_le_rel y x.
Proof.
  intros X Y.
  split.
  - intros Hnlt y Yy.
    generalize (is_Dcuts_open _ _ Yy) ; apply hinhuniv ; intros (y',(Yy',Hy)).
    apply minusNonnegativeRationals_gt0 in Hy.
    generalize (is_Dcuts_error X _ Hy) ; apply hinhuniv ; intros [nXc | ].
    + apply fromempty, Hnlt.
      apply hinhpr.
      exists y' ; split.
      * intro Xy' ; apply nXc.
        apply is_Dcuts_bot with (1 := Xy').
        now apply minusNonnegativeRationals_le.
      * exact Yy'.
    + apply hinhuniv ; intros (x,(Xx,Hx)).
      apply is_Dcuts_bot with (1 := Xx).
      apply notlt_geNonnegativeRationals ; intro H ; apply Hnlt.
      apply hinhpr.
      exists (x + (y' - y)) ; split.
      * exact Hx.
      * apply is_Dcuts_bot with (1 := Yy').
        pattern y' at 2 ; rewrite <- (minusNonegativeRationals_plus_r y y').
        rewrite iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals, H.
        apply lt_leNonnegativeRationals ; apply_pr2 minusNonnegativeRationals_gt0.
        exact Hy.
  - intros Hxy ; unfold neg.
    apply (hinhuniv (P := hProppair _ isapropempty)) ;
    intros (r,(Yr,Xr)).
    now apply Yr, Hxy.
Qed.

Lemma istrans_Dcuts_lt_le_rel :
  ∀ x y z : Dcuts_set, Dcuts_lt_rel x y -> Dcuts_le_rel y z -> Dcuts_lt_rel x z.
Proof.
  intros x y z Hlt Hle.
  revert Hlt ; apply hinhfun ; intros (r,(nXr,Yr)).
  exists r ; split.
  - exact nXr.
  - now apply Hle.
Qed.
Lemma istrans_Dcuts_le_lt_rel :
  ∀ x y z : Dcuts_set, Dcuts_le_rel x y -> Dcuts_lt_rel y z -> Dcuts_lt_rel x z.
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
    + exact Dcuts_lt_le_rel.
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
  λ X Y : Dcuts_set, ∀ r : NonnegativeRationals, (r ∈ X -> r ∈ Y) × (r ∈ Y -> r ∈ X).
Lemma isaprop_Dcuts_eq_rel : ∀ X Y : Dcuts_set, isaprop (Dcuts_eq_rel X Y).
Proof.
  intros X Y.
  apply impred_isaprop ; intro r.
  apply isapropdirprod.
  - now apply isapropimpl, pr2.
  - now apply isapropimpl, pr2.
Qed.
Definition Dcuts_eq : hrel Dcuts_set :=
  λ X Y : Dcuts_set, hProppair (∀ r, dirprod (r ∈ X -> r ∈ Y) (r ∈ Y -> r ∈ X)) (isaprop_Dcuts_eq_rel X Y).

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
  ∀ x y : Dcuts_set,
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

Lemma istight_Dcuts_ap_rel : istight Dcuts_ap_rel.
Proof.
  intros X Y Hap.
  apply Dcuts_eq_is_eq.
  intros r ; split ; revert r.
  - change (X <= Y).
    apply Dcuts_le_ngt_rel.
    intro Hlt ; apply Hap.
    now apply hinhpr ; right.
  - change (Y <= X).
    apply Dcuts_le_ngt_rel.
    intro Hlt ; apply Hap.
    now apply hinhpr ; left.
Qed.

Definition Dcuts : tightapSet :=
  Dcuts_set ,, Dcuts_ap_rel ,,
    (isirrefl_Dcuts_ap_rel ,, issymm_Dcuts_ap_rel ,, iscotrans_Dcuts_ap_rel) ,,
    istight_Dcuts_ap_rel.

Lemma not_Dcuts_ap_eq :
  forall x y : Dcuts, ¬ (x ≠ y) -> (x = y).
Proof.
  intros x y.
  now apply istight_Dcuts_ap_rel.
Qed.

(** *** Various theorems about order *)

Lemma Dcuts_ge_le :
  ∀ x y : Dcuts, x >= y -> y <= x.
Proof.
  easy.
Qed.
Lemma Dcuts_le_ge :
  ∀ x y : Dcuts, x <= y -> y >= x.
Proof.
  easy.
Qed.
Lemma Dcuts_eq_le :
  ∀ x y : Dcuts, Dcuts_eq x y -> x <= y.
Proof.
  intros x y Heq.
  intro r ;
    now apply (pr1 (Heq _)).
Qed.
Lemma Dcuts_eq_ge :
  ∀ x y : Dcuts, Dcuts_eq x y -> x >= y.
Proof.
  intros x y Heq.
  apply Dcuts_eq_le.
  now apply issymm_Dcuts_eq.
Qed.
Lemma Dcuts_le_ge_eq :
  ∀ x y : Dcuts, x <= y -> x >= y -> x = y.
Proof.
  intros x y le_xy ge_xy.
  apply Dcuts_eq_is_eq.
  split.
  now apply le_xy.
  now apply ge_xy.
Qed.

Lemma Dcuts_gt_lt :
  ∀ x y : Dcuts, (x > y) <-> (y < x).
Proof.
  now split.
Qed.
Lemma Dcuts_gt_ge :
  ∀ x y : Dcuts, x > y -> x >= y.
Proof.
  intros x y.
  now apply Dcuts_lt_le_rel.
Qed.

Lemma Dcuts_gt_nle :
  ∀ x y : Dcuts, x > y -> neg (x <= y).
Proof.
  intros x y Hlt Hle.
  now apply (pr2 (Dcuts_le_ngt_rel _ _)) in Hle.
Qed.
Lemma Dcuts_nlt_ge :
  ∀ x y : Dcuts, neg (x < y) <-> (x >= y).
Proof.
  intros X Y.
  now apply Dcuts_le_ngt_rel.
Qed.
Lemma Dcuts_lt_nge :
  ∀ x y : Dcuts, x < y -> neg (x >= y).
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
    assert (Hn0 : (0 < q - r)%NRat) by (now apply minusNonnegativeRationals_gt0).
    intros P HP ; apply HP ; clear P HP.
    exists (q - r).
    split.
    + apply_pr2 (plusNonnegativeRationals_ltcompat_r r).
      rewrite minusNonegativeRationals_plus_r.
      pattern q at 1 ;
        rewrite <- isrunit_zeroNonnegativeRationals.
      apply plusNonnegativeRationals_ltcompat_l.
      exact Hr0.
      now apply lt_leNonnegativeRationals, Hqr.
    + rewrite minusNonegativeRationals_plus_r.
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
  ∀ q q' : NonnegativeRationals,
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
  ∀ q q' : NonnegativeRationals,
    NonnegativeRationals_to_Dcuts q ≠ NonnegativeRationals_to_Dcuts q'
    -> q != q'.
Proof.
  intros q q'.
  apply (hinhuniv (P := hProppair _ (isapropneg _))).
  intros [Hap | Hap].
  now apply ltNonnegativeRationals_noteq, isapfun_NonnegativeRationals_to_Dcuts_aux.
  now apply gtNonnegativeRationals_noteq, isapfun_NonnegativeRationals_to_Dcuts_aux.
Qed.
Lemma isapfun_NonnegativeRationals_to_Dcuts' :
  ∀ q q' : NonnegativeRationals,
    q != q'
    -> NonnegativeRationals_to_Dcuts q ≠ NonnegativeRationals_to_Dcuts q'.
Proof.
  intros q q' H.
  apply hinhpr.
  apply noteq_ltorgtNonnegativeRationals in H.
  destruct H.
  now left ; apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)).
  now right ; apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)).
Qed.

Definition Dcuts_zero : Dcuts := NonnegativeRationals_to_Dcuts 0%NRat.
Definition Dcuts_one : Dcuts := NonnegativeRationals_to_Dcuts 1%NRat.

Notation "0" := Dcuts_zero : Dcuts_scope.
Notation "1" := Dcuts_one : Dcuts_scope.

(** Various usefull theorems *)

Lemma Dcuts_zero_empty :
  forall r : NonnegativeRationals, neg (r ∈ 0).
Proof.
  intros r ; simpl.
  change (neg (r < 0)%NRat).
  now apply isnonnegative_NonnegativeRationals'.
Qed.
Lemma Dcuts_notempty_notzero :
  forall (x : Dcuts) (r : NonnegativeRationals), r ∈ x -> x != 0.
Proof.
  intros x r Hx Hx0.
  apply (fun H => is_Dcuts_bot _ _ H 0%NRat) in Hx.
  rewrite Hx0 in Hx.
  now apply (Dcuts_zero_empty 0%NRat) in Hx.
  now apply isnonnegative_NonnegativeRationals.
Qed.

Lemma Dcuts_apzero_notempty :
  forall (x : Dcuts), (0%NRat ∈ x) <-> x ≠ 0.
Proof.
  intros x ; split.
  - intro Hx.
    apply hinhpr ; right.
    apply hinhpr ; exists 0%NRat ; split.
    now apply Dcuts_zero_empty.
    exact Hx.
  - apply hinhuniv ; intros [ | ].
    + apply hinhuniv ; intros (r,(_,Or)).
      now apply Dcuts_zero_empty in Or.
    + apply hinhuniv ; intros (r,(_,Xr)).
      apply is_Dcuts_bot with (1 := Xr).
      now apply isnonnegative_NonnegativeRationals.
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
  apply NQhalf_is_pos in Hc.
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
      apply (pr2 ( lt_gtNonnegativeRationals _ _)).
      apply (multNonnegativeRationals_ltcompat_l x ry (q + c / x)%NRat Hx).
      apply notge_ltNonnegativeRationals.
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
  apply NQhalf_is_pos in Hc0.
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
  - revert Hy ; apply hinhuniv ; intros (y,(Yy,nYy)).
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
      revert H ; apply hinhfun ; intros (x,(Xx,nXx)).
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
  - revert Hx ; apply hinhuniv ; intros (x,(Xx,nXx)).
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
        hexists (λ l : NonnegativeRationals, (∀ rx : NonnegativeRationals, X rx -> (r * rx <= l)%NRat)
                                               × (0 < l)%NRat × (l < 1)%NRat).

Local Lemma Dcuts_inv_in :
  ∀ x, (0 < x)%NRat -> X x -> (Dcuts_inv_val (/ x)%NRat) -> empty.
Proof.
  intros x Hx0 Xx.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (l,(H,(Hl0,Hl1))).
  specialize (H _ Xx).
  rewrite islinv_NonnegativeRationals in H.
  apply (pr2 (notlt_geNonnegativeRationals _ _)) in H.
  now apply H, Hl1.
  exact Hx0.
Qed.
Local Lemma Dcuts_inv_out :
  ∀ x, ¬ (X x) -> ∀ y, (x < y)%NRat -> Dcuts_inv_val (/ y)%NRat.
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
  assert (∀ c, (0 < c)%NRat -> hexists (λ q : NonnegativeRationals, X q × ¬ X (q + c))).
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
  apply NQhalf_is_pos in Hc0.
  specialize (X_error _ Hc0) ; revert X_error.
  apply hinhfun ; intros (r,(Xr,nXr)).
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
    now apply_pr2 NQhalf_is_pos.
    pattern 1%NRat at 1 ;
      rewrite <- (islunit_oneNonnegativeRationals 1%NRat).
    apply istrans_le_lt_ltNonnegativeRationals with (NQmax 1 r * 1)%NRat.
    now apply multNonnegativeRationals_lecompat_r, NQmax_le_l.
    apply multNonnegativeRationals_ltcompat_l.
    exact Hmax.
    apply istrans_le_lt_ltNonnegativeRationals with (1 := NQmax_le_l _ r).
    apply plusNonnegativeRationals_lt_r.
    now apply_pr2 NQhalf_is_pos.
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

Lemma iscomm_Dcuts_plus : iscomm Dcuts_plus.
Proof.
  assert (H : ∀ x y, ∀ x0 : NonnegativeRationals, x0 ∈ Dcuts_plus x y -> x0 ∈ Dcuts_plus y x).
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
  ∀ x : Dcuts, Dcuts_mult Dcuts_zero x = Dcuts_zero.
Proof.
  intros x.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - apply hinhuniv ; intros ((ri,rx),(Hr,(Or,Xr))).
    now apply Dcuts_zero_empty in Or.
  - intro Hr.
    now apply Dcuts_zero_empty in Hr.
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
  ∀ x : Dcuts, ∀ Hx0 : x ≠ 0, Dcuts_mult (Dcuts_inv x Hx0) x = 1.
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
        apply_pr2 (multNonnegativeRationals_ltcompat_l 2).
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
        apply minusNonnegativeRationals_gt0.
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
  ∀ x : Dcuts, ∀ Hx0 : x ≠ 0, Dcuts_mult x (Dcuts_inv x Hx0) = 1.
Proof.
  intros x Hx0.
  rewrite iscomm_Dcuts_mult.
  now apply islinv_Dcuts_inv.
Qed.

Lemma Dcuts_plus_ltcompat_l :
  ∀ x y z: Dcuts, (y < z) <-> (Dcuts_plus y x < Dcuts_plus z x).
Proof.
  intros x y z.
  split.
  - apply hinhuniv ; intros (r,(nYr,Zr)).
    generalize (is_Dcuts_open _ _ Zr) ; apply hinhuniv ; intros (r',(Zr',Hr)).
    apply minusNonnegativeRationals_gt0 in Hr.
    generalize (is_Dcuts_error x _ Hr).
    apply hinhuniv ; intros [nXc | ].
    + apply hinhpr ; exists r' ; split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ] ; apply hinhuniv ; [intros [Yr' | Xr'] | intros ((ry,rx),(Hr',(Yr',Xr')))].
        apply nYr, is_Dcuts_bot with (1 := Yr'), lt_leNonnegativeRationals.
        now apply_pr2 minusNonnegativeRationals_gt0.
        apply nXc, is_Dcuts_bot with (1 := Xr'), minusNonnegativeRationals_le.
        simpl in Hr',Yr',Xr'.
        revert Hr' ; apply gtNonnegativeRationals_noteq.
        rewrite <- (minusNonegativeRationals_plus_r r r'), iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_ltcompat.
        now apply (Dcuts_finite y).
        now apply (Dcuts_finite x).
        apply lt_leNonnegativeRationals.
        now apply_pr2 minusNonnegativeRationals_gt0.
      * apply hinhpr ; left.
        now apply hinhpr ; left.
    + apply hinhfun ; intros (q,(Xq,nXq)).
      exists (r' + q)%NRat ; split.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ] ; apply hinhuniv ; [intros [Yr' | Xr'] | intros ((ry,rx),(Hr',(Yr',Xr')))].
        apply nYr, is_Dcuts_bot with (1 := Yr'), lt_leNonnegativeRationals.
        rewrite <- (isrunit_zeroNonnegativeRationals r).
        apply plusNonnegativeRationals_lt_le_ltcompat.
        now apply_pr2 minusNonnegativeRationals_gt0.
        now apply isnonnegative_NonnegativeRationals.
        apply nXq, is_Dcuts_bot with (1 := Xr').
        rewrite iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_r.
        now apply minusNonnegativeRationals_le.
        simpl in Hr',Yr',Xr'.
        revert Hr' ; apply gtNonnegativeRationals_noteq.
        rewrite iscomm_plusNonnegativeRationals, <- (minusNonegativeRationals_plus_r r r'), <- isassoc_plusNonnegativeRationals, iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_ltcompat.
        now apply (Dcuts_finite y).
        now apply (Dcuts_finite x).
        apply lt_leNonnegativeRationals.
        now apply_pr2 minusNonnegativeRationals_gt0.
      * apply hinhpr ; right.
        apply hinhpr ; exists (r',q) ; repeat split.
        exact Zr'.
        exact Xq.
  - now apply Dcuts_plus_lt_l.
Qed.
Lemma Dcuts_plus_lecompat_l :
  ∀ x y z: Dcuts, (y <= z) <-> (Dcuts_plus y x <= Dcuts_plus z x).
Proof.
  intros x y z.
  split.
  - intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
    now apply_pr2 (Dcuts_plus_ltcompat_l x).
  - intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
    now apply Dcuts_plus_ltcompat_l.
Qed.
Lemma Dcuts_plus_ltcompat_r :
  ∀ x y z: Dcuts, (y < z) <-> (Dcuts_plus x y < Dcuts_plus x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_plus x).
  now apply Dcuts_plus_ltcompat_l.
Qed.
Lemma Dcuts_plus_lecompat_r :
  ∀ x y z: Dcuts, (y <= z) <-> (Dcuts_plus x y <= Dcuts_plus x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_plus x).
  now apply Dcuts_plus_lecompat_l.
Qed.

Lemma Dcuts_mult_ltcompat_l :
  ∀ x y z: Dcuts, (0 < x) -> (y < z) -> (Dcuts_mult y x < Dcuts_mult z x).
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
      now apply minusNonnegativeRationals_gt0.
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
  ∀ x y z: Dcuts, (Dcuts_mult y x < Dcuts_mult z x) -> (y < z).
Proof.
  intros x y z.
  now apply Dcuts_mult_lt_l.
Qed.
Lemma Dcuts_mult_lecompat_l :
  ∀ x y z: Dcuts, (0 < x) -> (Dcuts_mult y x <= Dcuts_mult z x) -> (y <= z).
Proof.
  intros x y z Hx0.
  intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
  now apply Dcuts_mult_ltcompat_l.
Qed.
Lemma Dcuts_mult_lecompat_l' :
  ∀ x y z: Dcuts, (y <= z) -> (Dcuts_mult y x <= Dcuts_mult z x).
Proof.
  intros x y z.
  intros H ; apply Dcuts_nlt_ge ; intro H0 ; apply (pr2 (Dcuts_nlt_ge _ _) H).
  now apply (Dcuts_mult_ltcompat_l' x).
Qed.

Lemma Dcuts_mult_ltcompat_r :
  ∀ x y z: Dcuts, (0 < x) -> (y < z) -> (Dcuts_mult x y < Dcuts_mult x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_ltcompat_l.
Qed.
Lemma Dcuts_mult_ltcompat_r' :
  ∀ x y z: Dcuts, (Dcuts_mult x y < Dcuts_mult x z) -> (y < z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_ltcompat_l'.
Qed.
Lemma Dcuts_mult_lecompat_r :
  ∀ x y z: Dcuts, (0 < x) -> (Dcuts_mult x y <= Dcuts_mult x z) -> (y <= z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_lecompat_l.
Qed.
Lemma Dcuts_mult_lecompat_r' :
  ∀ x y z: Dcuts, (y <= z) -> (Dcuts_mult x y <= Dcuts_mult x z).
Proof.
  intros x y z.
  rewrite ! (iscomm_Dcuts_mult x).
  now apply Dcuts_mult_lecompat_l'.
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
  fun r => hexists (λ x, X x × ∀ y, (Y y) ⨿ (y = 0%NRat) -> (r < x - y)%NRat).

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
        rewrite iscomm_plusNonnegativeRationals, minusNonegativeRationals_plus_r.
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
    now apply minusNonnegativeRationals_gt0.
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
    - right ; revert Hy ; apply hinhfun ; intros (y,(Yy,nYy)).
      exists y ; split.
      + now apply hinhpr ; left.
      + intros H ; apply nYy ; revert H.
        apply hinhuniv ; intros [H | Hc0].
        * exact H.
        * apply fromempty ; revert Hc0.
          apply gtNonnegativeRationals_noteq.
          now apply ispositive_plusNonnegativeRationals_r. }
  intros c Hc.
  apply NQhalf_is_pos in Hc.
  apply (fun X X0 Xerr => Dcuts_def_error_not_empty X X0 Xerr _ Hc) in Y_error'.
  revert Y_error' ; apply hinhuniv ; intros (y,(Yy,nYy)).
  revert Yy ; apply hinhuniv ; intros Yy.
  assert (¬ Y (y + c / 2)).
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
  - revert Hx ; apply hinhfun ; intros (x,(Xx,nXx)).
    case (isdecrel_leNonnegativeRationals (y + c / 2) x) ; intro Hxy.
    + assert (HY : ∀ y', coprod (Y y') (y' = 0%NRat) -> (y' < y + c / 2)%NRat).
      { intros y' [Yy' | Yy'].
        apply notge_ltNonnegativeRationals ; intro H ; apply nYy.
        now apply Y_bot with (1 := Yy').
        rewrite Yy'.
        now apply ispositive_plusNonnegativeRationals_r. }
      right ; apply hinhpr ; exists (x - (y + c / 2)) ; split.
      * apply hinhpr.
        exists x ; split.
        exact Xx.
        intros y' Yy'.
        apply minusNonnegativeRationals_ltcompat_r.
        now apply HY.
        apply istrans_lt_le_ltNonnegativeRationals with (y + c / 2).
        now apply HY.
        exact Hxy.
      * unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x',(Xx',Hx')).
        specialize (Hx' y Yy).
        revert Hx'.
        change (¬ (x - (y + c / 2) + c < x' - y)%NRat).
        apply (pr2 (notlt_geNonnegativeRationals _ _)).
        apply istrans_leNonnegativeRationals with ((x + c / 2) - y).
        apply minusNonnegativeRationals_lecompat_l.
        apply lt_leNonnegativeRationals.
        apply notge_ltNonnegativeRationals ; intro H ; apply nXx.
        now apply X_bot with (1 := Xx').
        rewrite minusNonnegativeRationals_plus_exchange.
        apply_pr2 (plusNonnegativeRationals_lecompat_r y).
        rewrite minusNonegativeRationals_plus_r.
        apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)).
        rewrite ! isassoc_plusNonnegativeRationals.
        rewrite <- NQhalf_double, minusNonegativeRationals_plus_r.
        now apply isrefl_leNonnegativeRationals.
        apply istrans_leNonnegativeRationals with x.
        exact Hxy.
        now apply plusNonnegativeRationals_le_r.
        apply_pr2 (plusNonnegativeRationals_lecompat_r (c / 2)).
        rewrite isassoc_plusNonnegativeRationals, <- NQhalf_double.
        apply istrans_leNonnegativeRationals with x.
        exact Hxy.
        now apply plusNonnegativeRationals_le_r.
        exact Hxy.
    + apply notge_ltNonnegativeRationals in Hxy.
      left ; unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x',(Xx',Hx')).
      generalize (Hx' _ Yy).
      change (¬ (c < x' - y)%NRat) ; apply (pr2 (notlt_geNonnegativeRationals _ _)).
      case (isdecrel_leNonnegativeRationals y x') ; intro Hxy'.
      apply_pr2 (plusNonnegativeRationals_lecompat_r y).
      rewrite minusNonegativeRationals_plus_r, iscomm_plusNonnegativeRationals, (NQhalf_double c), <- isassoc_plusNonnegativeRationals.
      apply istrans_leNonnegativeRationals with (x + c / 2).
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
  ∀ x y z : Dcuts, x = Dcuts_plus y z -> z = Dcuts_minus x y.
Proof.
  intros _ Y Z ->.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - intros Zr.
    generalize (is_Dcuts_open _ _ Zr) ; apply hinhuniv ; intros (q,(Zq,Hq)).
    apply minusNonnegativeRationals_gt0 in Hq.
    generalize (is_Dcuts_error Y _ Hq) ; apply hinhuniv ; intros [nYy | ].
    + apply hinhpr ; exists q ; split.
      * apply hinhpr ; left.
        now apply hinhpr ; right.
      * intros y [Yy | Hy0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r y).
        rewrite minusNonegativeRationals_plus_r.
        apply minusNonnegativeRationals_ltcompat_l' with r.
        rewrite plusNonnegativeRationals_minus_l.
        now apply (Dcuts_finite Y).
        apply istrans_leNonnegativeRationals with (q - r).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Y).
        now apply minusNonnegativeRationals_le.
        rewrite Hy0, minusNonnegativeRationals_zero_r.
        now apply_pr2 minusNonnegativeRationals_gt0.
    + apply hinhfun ; intros (y,(Yy,Hy)).
      exists (y + q) ; split.
      apply hinhpr ; right.
      apply hinhpr ; exists (y,q) ; simpl ; repeat split.
      * exact Yy.
      * exact Zq.
      * intros y' [Yy' | Hy0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r y').
        rewrite minusNonegativeRationals_plus_r.
        apply minusNonnegativeRationals_ltcompat_l' with r.
        rewrite plusNonnegativeRationals_minus_l.
        rewrite iscomm_plusNonnegativeRationals, <- minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals.
        now apply (Dcuts_finite Y).
        now apply lt_leNonnegativeRationals ; apply_pr2 minusNonnegativeRationals_gt0.
        apply istrans_leNonnegativeRationals with (y + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Y).
        apply plusNonnegativeRationals_lecompat_l.
        now apply minusNonnegativeRationals_le.
        rewrite Hy0, minusNonnegativeRationals_zero_r.
        apply istrans_lt_le_ltNonnegativeRationals with q.
        now apply_pr2 minusNonnegativeRationals_gt0.
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
  ∀ x y z : Dcuts, x = Dcuts_plus y z -> y = Dcuts_minus x z.
Proof.
  intros x y z Hx.
  apply Dcuts_minus_correct_l.
  rewrite Hx.
  now apply iscomm_Dcuts_plus.
Qed.
Lemma Dcuts_minus_eq_zero:
  ∀ x y : Dcuts, x <= y -> Dcuts_minus x y = 0.
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
  ∀ x y z : Dcuts, z <= y -> x = Dcuts_minus y z -> y = Dcuts_plus x z.
Proof.
  intros _ Y Z Hyz ->.
  apply Dcuts_eq_is_eq ; intro r ; split.
  - intros Yr.
    generalize (is_Dcuts_open _ _ Yr) ; apply hinhuniv ; intros (q,(Yq,Hq)).
    apply minusNonnegativeRationals_gt0 in Hq.
    generalize (is_Dcuts_error Z _ Hq).
    apply hinhuniv ; intros [nZ | ].
    + apply hinhpr ; left.
      apply hinhpr ; left.
      apply hinhpr.
      exists q ; split.
      exact Yq.
      intros z [Zz | Hz0].
      * apply_pr2 (plusNonnegativeRationals_ltcompat_r z).
        rewrite minusNonegativeRationals_plus_r.
        apply (minusNonnegativeRationals_ltcompat_l' _ _ r).
        rewrite plusNonnegativeRationals_minus_l.
        now apply (Dcuts_finite Z).
        apply istrans_leNonnegativeRationals with (q - r).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        now apply minusNonnegativeRationals_le.
      * now rewrite Hz0, minusNonnegativeRationals_zero_r ; apply_pr2 minusNonnegativeRationals_gt0.
    + apply hinhuniv ; intros (z,(Zz,nZz)).
      case (isdecrel_leNonnegativeRationals r z) ; intro Hzr.
      * apply hinhpr ; left.
        apply hinhpr ; right.
        now apply (is_Dcuts_bot _ _ Zz).
      * apply notge_ltNonnegativeRationals in Hzr ; apply lt_leNonnegativeRationals in Hzr.
        apply hinhpr ; right.
        apply hinhpr.
        exists (r - z , z) ; repeat split.
        simpl.
        now rewrite minusNonegativeRationals_plus_r.
        apply hinhpr ; simpl.
        exists q ; split.
        exact Yq.
        intros z' [Zz' | Hz0].
        apply_pr2 (plusNonnegativeRationals_ltcompat_r z).
        rewrite minusNonegativeRationals_plus_r.
        rewrite minusNonnegativeRationals_plus_exchange.
        apply_pr2 (plusNonnegativeRationals_ltcompat_r z').
        rewrite minusNonegativeRationals_plus_r.
        apply (minusNonnegativeRationals_ltcompat_l' _ _ r) ; rewrite plusNonnegativeRationals_minus_l.
        rewrite <- minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals.
        now apply (Dcuts_finite Z).
        now apply lt_leNonnegativeRationals ; apply_pr2 minusNonnegativeRationals_gt0.
        apply istrans_leNonnegativeRationals with (z + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        rewrite iscomm_plusNonnegativeRationals, minusNonnegativeRationals_plus_exchange.
        now apply minusNonnegativeRationals_le.
        now apply lt_leNonnegativeRationals ; apply_pr2 minusNonnegativeRationals_gt0.
        apply istrans_leNonnegativeRationals with (z + (q - r)).
        now apply lt_leNonnegativeRationals, (Dcuts_finite Z).
        pattern q at 2 ;
          rewrite <- (minusNonegativeRationals_plus_r r q), iscomm_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        exact Hzr.
        now apply lt_leNonnegativeRationals ; apply_pr2 minusNonnegativeRationals_gt0.
        exact Hzr.
        rewrite Hz0, minusNonnegativeRationals_zero_r.
        apply istrans_le_lt_ltNonnegativeRationals with r.
        now apply minusNonnegativeRationals_le.
        now apply_pr2 minusNonnegativeRationals_gt0.
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
  ∀ x y, Dcuts_minus x y <= x.
Proof.
  intros X Y r.
  apply hinhuniv ; intros (x,(Xx,Hx)).
  apply is_Dcuts_bot with (1 := Xx).
  apply lt_leNonnegativeRationals ; rewrite <- (minusNonnegativeRationals_zero_r x).
  apply Hx.
  now right.
Qed.

Lemma ispositive_Dcuts_minus :
  ∀ x y : Dcuts, (y < x) <-> (0 < Dcuts_minus x y).
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
      * apply minusNonnegativeRationals_gt0.
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
  - right ; revert Hy ; apply hinhfun ; intros (y,(Yy,nYy)).
    exists y ; split.
    + now apply hinhpr ; right.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xy | Yy'].
      * now apply nXc, X_bot with (1 := Xy), plusNonnegativeRationals_le_l.
      * now apply nYy.
  - right ; revert Hx ; apply hinhfun ; intros (x,(Xx,nXx)).
    exists x ; split.
    + now apply hinhpr ; left.
    + unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [Xx' | Yx].
      * now apply nXx.
      * now apply nYc, Y_bot with (1 := Yx), plusNonnegativeRationals_le_l.
  - right ; revert Hx Hy ; apply hinhfun2 ; intros (x,(Xx,nXx)) (y,(Yy,nYy)).
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
  ∀ x y : Dcuts, Dcuts_max x y = Dcuts_max y x.
Proof.
  intros x y.
  apply Dcuts_eq_is_eq ; intros r.
  split ; apply islogeqcommhdisj.
Qed.

Lemma Dcuts_max_carac_l :
  ∀ x y : Dcuts, y <= x -> Dcuts_max x y = x.
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
  ∀ x y : Dcuts, x <= y -> Dcuts_max x y = y.
Proof.
  intros x y Hxy.
  rewrite iscomm_Dcuts_max.
  now apply Dcuts_max_carac_l.
Qed.

Lemma Dcuts_minus_plus_max :
  ∀ x y : Dcuts, Dcuts_plus (Dcuts_minus x y) y = Dcuts_max x y.
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
      apply minusNonnegativeRationals_gt0 in Hx.
      generalize (is_Dcuts_error Y _ Hx) ; apply hinhuniv ;
      intros [nYx | Hyx ] ; apply_pr2_in minusNonnegativeRationals_gt0 Hx.
      * rewrite <- (Dcuts_minus_plus_r (Dcuts_minus X Y) X Y).
        exact Xr.
        apply Dcuts_lt_le_rel.
        apply hinhpr ; exists (x - r) ; split.
        exact nYx.
        apply is_Dcuts_bot with (1 := Xx).
        now apply minusNonnegativeRationals_le.
        reflexivity.
      * revert Hyx ; apply hinhuniv ; intros (y,(Yy,nYy)).
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

(** *** Dcuts_half *)

Definition Dcuts_two : Dcuts :=
  NonnegativeRationals_to_Dcuts 2.
Lemma Dcuts_two_ap_zero : Dcuts_two ≠ 0.
Proof.
  apply isapfun_NonnegativeRationals_to_Dcuts'.
  apply gtNonnegativeRationals_noteq.
  exact ispositive_twoNonnegativeRationals.
Qed.

Definition Dcuts_half (x : Dcuts) : Dcuts := Dcuts_mult x (Dcuts_inv Dcuts_two Dcuts_two_ap_zero).

Lemma ispositive_Dcuts_half:
  ∀ x : Dcuts, (0 < x) <-> (0 < Dcuts_half x).
Proof.
  intros.
  unfold Dcuts_half.
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
Lemma isdistr_Dcuts_half_plus :
  forall x y : Dcuts, Dcuts_half (Dcuts_plus x y) = Dcuts_plus (Dcuts_half x) (Dcuts_half y).
Admitted.
Lemma isdistr_Dcuts_half_minus :
  forall x y : Dcuts, Dcuts_half (Dcuts_minus x y) = Dcuts_minus (Dcuts_half x) (Dcuts_half y).
Admitted.
Lemma double_Dcuts_half :
  ∀ x : Dcuts, x = Dcuts_plus (Dcuts_half x) (Dcuts_half x).
Admitted.


(** ** Least Upper Finite *)

Lemma CauchySubset_equiv (E : hsubtypes Dcuts) :
  (∀ c, 0 < c -> (isUpperBound (X := eo_Dcuts) E c) ∨ (hexists (λ P, E P × isUpperBound (X := eo_Dcuts) E (Dcuts_plus P c)))) =
  (∀ c, (0 < c)%NRat -> (isUpperBound (X := eo_Dcuts) E (NonnegativeRationals_to_Dcuts c)) ∨ (hexists (λ P, E P × isUpperBound (X := eo_Dcuts) E (Dcuts_plus P  (NonnegativeRationals_to_Dcuts c))))).
Proof.
  intro E.
  apply uahp'.
  - apply impred_isaprop ; intro c.
    apply isapropimpl.
    now apply pr2.
  - apply impred_isaprop ; intro c.
    apply isapropimpl.
    now apply pr2.
  - intros H c Hc.
    apply H.
    now apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)).
  - intros H C HC.
    revert HC ; apply hinhuniv ; intros (c',(_,Cc')).
    generalize (is_Dcuts_open _ _ Cc') ; apply hinhuniv ; intros (c,(Cc,Hc)).
    assert (Hc0 : (0 < c)%NRat).
    { apply istrans_le_lt_ltNonnegativeRationals with c'.
      now apply isnonnegative_NonnegativeRationals.
      exact Hc. }
    clear c' Cc' Hc.
    generalize (H _ Hc0) ; apply hinhfun ; intros [Ec | H0].
    + left ; intros x Hx r Xr.
      specialize (Ec x Hx r Xr).
      apply is_Dcuts_bot with (1 := Cc).
      apply lt_leNonnegativeRationals, Ec.
    + right ; revert H0.
      apply hinhfun ; intros (x,(Ex,Hx)).
      exists x ; split.
      exact Ex.
      intros y Ey.
      apply istrans_Dcuts_le_rel with (Dcuts_plus x (NonnegativeRationals_to_Dcuts c)).
      now apply Hx.
      change ((Dcuts_plus x (NonnegativeRationals_to_Dcuts c)) <= (Dcuts_plus x C)).
      apply Dcuts_plus_lecompat_r.
      intros r Hr.
      apply is_Dcuts_bot with (1 := Cc).
      now apply lt_leNonnegativeRationals, Hr.
Qed.

Section Dcuts_lub.

Context (E : hsubtypes Dcuts).
Context (E_bounded : hexists (isUpperBound (X := eo_Dcuts) E)).
Context (E_cauchy: ∀ c, 0 < c -> (isUpperBound (X := eo_Dcuts) E c) ∨ (hexists (λ P, E P × isUpperBound (X := eo_Dcuts) E (Dcuts_plus P c)))).

Definition Dcuts_lub_val : NonnegativeRationals -> hProp :=
  fun r : NonnegativeRationals => hexists (λ X : Dcuts, (E X) × (r ∈ X)).

Lemma Dcuts_lub_bot :
  ∀ (x : NonnegativeRationals),
    Dcuts_lub_val x -> ∀ y : NonnegativeRationals, (y <= x)%NRat -> Dcuts_lub_val y.
Proof.
  intros r Xr n Xn.
  revert Xr ; apply hinhfun ; intros (X,(Ex,Xr)).
  exists X ; split.
  exact Ex.
  now apply is_Dcuts_bot with r.
Qed.

Lemma Dcuts_lub_open :
  ∀ (x : NonnegativeRationals),
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
Lemma Dcuts_lub_error:
  Dcuts_def_error Dcuts_lub_val.
Proof.
  intros c Hc.
  apply NQhalf_is_pos in Hc.
  apply (pr2 (isapfun_NonnegativeRationals_to_Dcuts_aux _ _)) in Hc.
  generalize (E_cauchy _ Hc).
  apply isapfun_NonnegativeRationals_to_Dcuts_aux in Hc.
  apply hinhuniv ; intros [He | ].
  intros P HP ; apply HP ; clear P HP.
  - left.
    unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (X,(EX,Xc)).
    specialize (He _ EX).
    generalize (He _ Xc) ; simpl.
    change (¬ (c < c / 2)%NRat).
    apply (pr2 (notlt_geNonnegativeRationals _ _)).
    pattern c at 2.
    rewrite (NQhalf_double c).
    apply plusNonnegativeRationals_le_r.
  - apply hinhuniv ; intros (X,(EX,Hx)).
    generalize (is_Dcuts_error X _ Hc).
    apply hinhfun ; intros [Xc | ].
    + left.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (Y,(EY,Yc)).
      generalize (Hx _ EY).
      intros H.
      generalize (H _ Yc).
      apply hinhuniv ; intros [ | ].
      apply hinhuniv ; intros [ Xc' | Yc' ].
      * apply Xc.
        apply is_Dcuts_bot with (1 := Xc').
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
      * revert Yc' ; simpl.
        change (¬ (c < c / 2)%NRat).
        apply (pr2 (notlt_geNonnegativeRationals _ _)).
        pattern c at 2.
        rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_le_r.
      * apply hinhuniv.
        intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply Xc, is_Dcuts_bot with (1 := Xc').
        apply_pr2 (plusNonnegativeRationals_lecompat_r cy).
        rewrite <- Hc'.
        pattern c at 2 ; rewrite (NQhalf_double c).
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals.
    + intro ; right.
      revert h ; apply hinhfun ; intros (q,(Xq,nXq)).
      exists q ; split.
      intros P HP ; apply HP ; clear P HP.
      now exists X ; split.
      unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (Y,(EY,Yc)).
      generalize (Hx _ EY).
      intros H.
      generalize (H _ Yc).
      apply hinhuniv ; intros [ | ].
      apply hinhuniv ; intros [ Xc' | Yc' ].
      * apply nXq.
        apply is_Dcuts_bot with (1 := Xc').
        pattern c at 2.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply plusNonnegativeRationals_le_r.
      * revert Yc' ; simpl.
        change (¬ ((q + c) < (c / 2))%NRat).
        apply (pr2 (notlt_geNonnegativeRationals _ _)).
        pattern c at 2.
        rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply plusNonnegativeRationals_le_l.
      * apply hinhuniv.
        intros ((cx,cy),(Hc',(Xc',Yc'))).
        simpl in Hc',Xc',Yc'.
        apply nXq, is_Dcuts_bot with (1 := Xc').
        apply_pr2 (plusNonnegativeRationals_lecompat_r cy).
        rewrite <- Hc'.
        pattern c at 2 ; rewrite (NQhalf_double c).
        rewrite <- isassoc_plusNonnegativeRationals.
        apply plusNonnegativeRationals_lecompat_l.
        now apply lt_leNonnegativeRationals.
Qed.

End Dcuts_lub.

Definition Dcuts_lub (E : hsubtypes Dcuts) E_cauchy : Dcuts :=
  mk_Dcuts (Dcuts_lub_val E) (Dcuts_lub_bot E) (Dcuts_lub_open E) (Dcuts_lub_error E E_cauchy).

Lemma isub_Dcuts_lub (E : hsubtypes Dcuts) E_cauchy :
  isUpperBound (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_lub E E_cauchy).
Proof.
  intros ;
  intros x Ex r Hr.
  apply hinhpr.
  now exists x.
Qed.
Lemma islbub_Dcuts_lub (E : hsubtypes Dcuts) E_cauchy :
  isSmallerThanUpperBounds (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_lub E E_cauchy).
Proof.
  intros.
  intros x Hx ; simpl.
  intros r ; apply hinhuniv ;
  intros (y,(Ey,Yr)).
  generalize (Hx y Ey).
  now intros H ; apply H.
Qed.
Lemma islub_Dcuts_lub (E : hsubtypes eo_Dcuts) E_cauchy :
  isLeastUpperBound (X := PreorderedSetEffectiveOrder eo_Dcuts) E (Dcuts_lub E E_cauchy).
Proof.
  split.
  exact (isub_Dcuts_lub E E_cauchy).
  exact (islbub_Dcuts_lub E E_cauchy).
Qed.

(* Not yet...
(** ** Greatest Lower Bound *)

Section Dcuts_glb.

  Context (E : hsubtypes Dcuts).
  Context (E_bounded : hexists (isUpperBound (X := eo_Dcuts) E)).
  Context (E_cauchy: ∀ c, 0 < c -> (isUpperBound (X := eo_Dcuts) E c) ∨ (hexists (λ P, E P × isUpperBound (X := eo_Dcuts) E (Dcuts_plus P c)))).
  Context (E_not_empty : hexists E).

Definition Dcuts_glb : GreatestLowerBound (X := eo_Dcuts) E.
Proof.
  assert (Hprop : isaprop (GreatestLowerBound (X := eo_Dcuts) E)).
  { apply isapropGreatestLowerBound.
    intros X Y Hle Hge.
    apply Dcuts_eq_is_eq ; intro r ; split.
    now apply Hge.
    now apply Hle. }
  revert E_bounded ; apply (hinhuniv (P := hProppair _ Hprop)) ; intros (ub, Hub).
  set (E' := (λ x, E (Dcuts_minus ub x))).
  assert (E'_cauchy : (∀ c : Dcuts,
                          0 < c ->
                          isUpperBound (X := eo_Dcuts) E' c
                          ∨ hexists (λ P : Dcuts, E' P × isUpperBound (X := eo_Dcuts) E' (Dcuts_plus P c)))).
  { intros c Hc.

  }
  exists (Dcuts_minus ub (Dcuts_lub E' E'_cauchy)).
Defined. *)

(** * Definition of non-negative real numbers *)

Definition NonnegativeReals : ConstructiveCommutativeDivisionRig := Dcuts_ConstructiveCommutativeDivisionRig.

Definition NonnegativeReals_to_hsubtypesNonnegativeRationals :
  NonnegativeReals -> (hsubtypes NonnegativeRationals) := pr1.
Definition hsubtypesNonnegativeRationals_to_NonnegativeReals
  (X : NonnegativeRationals -> hProp)
  (Xbot : ∀ x : NonnegativeRationals,
            X x -> ∀ y : NonnegativeRationals, (y <= x)%NRat -> X y)
  (Xopen : ∀ x : NonnegativeRationals,
             X x ->
             hexists (fun y : NonnegativeRationals => dirprod (X y) (x < y)%NRat))
  (Xtop : Dcuts_def_error X) : NonnegativeReals :=
  mk_Dcuts X Xbot Xopen Xtop.

(** ** Constants and functions *)

Definition apNonnegativeReals : hrel NonnegativeReals := CCDRap.
Definition zeroNonnegativeReals : NonnegativeReals := CCDRzero.
Definition oneNonnegativeReals : NonnegativeReals := CCDRone.
Definition twoNonnegativeReals : NonnegativeReals := Dcuts_two.
Definition plusNonnegativeReals : binop NonnegativeReals := CCDRplus.
Definition minusNonnegativeReals : binop NonnegativeReals := Dcuts_minus.
Definition multNonnegativeReals : binop NonnegativeReals := CCDRmult.
Definition halfNonnegativeReals : unop NonnegativeReals := Dcuts_half.

Delimit Scope NR_scope with NR.
Open Scope NR_scope.

Notation "x ≠ y" := (apNonnegativeReals x y) (at level 70, no associativity) : NR_scope.
Notation "0" := zeroNonnegativeReals : NR_scope.
Notation "1" := oneNonnegativeReals : NR_scope.
Notation "2" := twoNonnegativeReals : NR_scope.
Notation "x + y" := (plusNonnegativeReals x y) (at level 50, left associativity) : NR_scope.
Notation "x - y" := (minusNonnegativeReals x y) (at level 50, left associativity) : NR_scope.
Notation "x * y" := (multNonnegativeReals x y) (at level 40, left associativity) : NR_scope.
Notation "x / 2" := (halfNonnegativeReals x) (at level 35, no associativity) : NR_scope.

Definition invNonnegativeReals (x : NonnegativeReals) (Hx0 : x ≠ 0) : NonnegativeReals :=
  CCDRinv x Hx0.
Definition divNonnegativeReals (x y : NonnegativeReals) (Hy0 : y ≠ 0) : NonnegativeReals :=
  multNonnegativeReals x (invNonnegativeReals y Hy0).

Definition maxNonnegativeReals : binop NonnegativeReals := Dcuts_max.

Definition leNonnegativeReals : po NonnegativeReals := Dcuts_le.
Definition geNonnegativeReals : po NonnegativeReals := Dcuts_ge.
Definition ltNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_lt.
Definition gtNonnegativeReals : StrongOrder NonnegativeReals := Dcuts_gt.

Definition lubNonnegativeReals (E : hsubtypes NonnegativeReals)
           (Eub : ∀ c : NonnegativeReals,
               0 < c ->
               isUpperBound (X := eo_Dcuts) E c
               ∨ hexists (λ x : Dcuts, E x × isUpperBound (X := eo_Dcuts) E (x + c))) :
  LeastUpperBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_lub E Eub) (islub_Dcuts_lub E Eub).

(*Definition glbNonnegativeReals (E : hsubtypes NonnegativeReals) (Ene : hexists E) : GreatestLowerBound (X := eo_Dcuts) E :=
  tpair _ (Dcuts_glb E Ene) (isglb_Dcuts_glb E Ene).*)

(** ** Theorems *)

Lemma notapNonnegativeReals_eq:
  ∀ x y : NonnegativeReals, (¬ (x ≠ y)) <-> (x = y).
Proof.
  intros x y.
  split.
  - now apply istight_Dcuts_ap_rel.
  - intros ->.
    now apply isirrefl_Dcuts_ap_rel.
Qed.

Definition isnonzeroNonnegativeReals: 1 ≠ 0
  := isnonzeroCCDR (X := NonnegativeReals).

Definition ap_plusNonnegativeReals:
  ∀ x x' y y' : NonnegativeReals,
    x + y ≠ x' + y' -> x ≠ x' ∨ y ≠ y' :=
  apCCDRplus (X := NonnegativeReals).
Definition ap_multNonnegativeReals:
  ∀ x x' y y' : NonnegativeReals,
    x * y ≠ x' * y' -> x ≠ x' ∨ y ≠ y'
  := apCCDRmult (X := NonnegativeReals).

Definition islunit_zero_plusNonnegativeReals:
  ∀ x : NonnegativeReals, 0 + x = x
  := islunit_CCDRzero_CCDRplus (X := NonnegativeReals).
Definition isrunit_zero_plusNonnegativeReals:
  ∀ x : NonnegativeReals, x + 0 = x
  := isrunit_CCDRzero_CCDRplus (X := NonnegativeReals).
Definition isassoc_plusNonnegativeReals:
  ∀ x y z : NonnegativeReals, x + y + z = x + (y + z)
  := isassoc_CCDRplus (X := NonnegativeReals).
Definition iscomm_plusNonnegativeReals:
  ∀ x y : NonnegativeReals, x + y = y + x
  := iscomm_CCDRplus (X := NonnegativeReals).

Definition ispositive_minusNonnegativeReals :
  ∀ x y : NonnegativeReals, (y < x) <-> (0 < x - y)
  := ispositive_Dcuts_minus.
Definition minusNonnegativeReals_le :
  ∀ x y : NonnegativeReals, x - y <= x
  := Dcuts_minus_le.
Definition minusNonnegativeReals_plus_r :
  ∀ x y z : NonnegativeReals, z <= y -> x = y - z -> y = x + z
  := Dcuts_minus_plus_r.
Definition minusNonnegativeReals_eq_zero :
  ∀ x y : NonnegativeReals, x <= y -> x - y = 0
  := Dcuts_minus_eq_zero.
Definition minusNonnegativeReals_correct_r :
  ∀ x y z : NonnegativeReals, x = y + z -> y = x - z
  := Dcuts_minus_correct_r.
Definition minusNonnegativeReals_correct_l :
  ∀ x y z : NonnegativeReals, x = y + z -> z = x - y
  := Dcuts_minus_correct_l.

Definition islunit_one_multNonnegativeReals:
  ∀ x : NonnegativeReals, 1 * x = x
  := islunit_CCDRone_CCDRmult (X := NonnegativeReals).
Definition isrunit_one_multNonnegativeReals:
  ∀ x : NonnegativeReals, x * 1 = x
  := isrunit_CCDRone_CCDRmult (X := NonnegativeReals).
Definition isassoc_multNonnegativeReals:
  ∀ x y z : NonnegativeReals, x * y * z = x * (y * z)
  := isassoc_CCDRmult (X := NonnegativeReals).
Definition iscomm_multNonnegativeReals:
  ∀ x y : NonnegativeReals, x * y = y * x
  := iscomm_CCDRmult (X := NonnegativeReals).
Definition islabsorb_zero_multNonnegativeReals:
  ∀ x : NonnegativeReals, 0 * x = 0
  := islabsorb_CCDRzero_CCDRmult (X := NonnegativeReals).
Definition israbsorb_zero_multNonnegativeReals:
  ∀ x : NonnegativeReals, x * 0 = 0
  := israbsorb_CCDRzero_CCDRmult (X := NonnegativeReals).

Definition islinv_invNonnegativeReals:
  ∀ (x : NonnegativeReals) (Hx0 : x ≠ 0), invNonnegativeReals x Hx0 * x = 1
  := islinv_CCDRinv (X := NonnegativeReals).
Definition isrinv_invNonnegativeReals:
  ∀ (x : NonnegativeReals) (Hx0 : x ≠ 0), x * invNonnegativeReals x Hx0 = 1
  := isrinv_CCDRinv (X := NonnegativeReals).

Definition isldistr_plus_multNonnegativeReals:
  ∀ x y z : NonnegativeReals, z * (x + y) = z * x + z * y
  := isldistr_CCDRplus_CCDRmult (X := NonnegativeReals).

Definition plusNonnegativeReals_ltcompat_l :
  ∀ x y z: NonnegativeReals, (y < z) <-> (y + x < z + x)
  := Dcuts_plus_ltcompat_l.
Definition plusNonnegativeReals_lecompat_l :
  ∀ x y z: NonnegativeReals, (y <= z) <-> (y + x <= z + x)
  := Dcuts_plus_lecompat_l.
Definition plusNonnegativeReals_ltcompat_r :
  ∀ x y z: NonnegativeReals, (y < z) <-> (x + y < x + z)
  := Dcuts_plus_ltcompat_r.
Definition plusNonnegativeReals_lecompat_r :
  ∀ x y z: NonnegativeReals, (y <= z) <-> (x + y <= x + z)
  := Dcuts_plus_lecompat_r.

Definition multNonnegativeReals_ltcompat_l :
  ∀ x y z: NonnegativeReals, (0 < x) -> (y < z) -> (y * x < z * x)
  := Dcuts_mult_ltcompat_l.
Definition multNonnegativeReals_ltcompat_l' :
  ∀ x y z: NonnegativeReals, (y * x < z * x) -> (y < z)
  := Dcuts_mult_ltcompat_l'.
Definition multNonnegativeReals_lecompat_l :
  ∀ x y z: NonnegativeReals, (0 < x) -> (y * x <= z * x) -> (y <= z)
  := Dcuts_mult_lecompat_l.
Definition multNonnegativeReals_lecompat_l' :
  ∀ x y z: NonnegativeReals, (y <= z) -> (y * x <= z * x)
  := Dcuts_mult_lecompat_l'.

Definition multNonnegativeReals_ltcompat_r :
  ∀ x y z: NonnegativeReals, (0 < x) -> (y < z) -> (x * y < x * z)
  := Dcuts_mult_ltcompat_r.
Definition multNonnegativeReals_ltcompat_r' :
  ∀ x y z: NonnegativeReals, (x * y < x *  z) -> (y < z)
  := Dcuts_mult_ltcompat_r'.
Definition multNonnegativeReals_lecompat_r :
  ∀ x y z: NonnegativeReals, (0 < x) -> (x * y <= x * z) -> (y <= z)
  := Dcuts_mult_lecompat_r.
Definition multNonnegativeReals_lecompat_r' :
  ∀ x y z: NonnegativeReals, (y <= z) -> (x * y <= x * z)
  := Dcuts_mult_lecompat_r'.

(** ** Convergence of Cauchy sequences *)

Definition Cauchy_seq (u : nat -> NonnegativeReals) : hProp
  := hProppair (∀ eps : NonnegativeReals,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            ∀ n m : nat, N ≤ n -> N ≤ m -> u n < u m + eps × u m < u n + eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).
Definition is_lim_seq (u : nat -> NonnegativeReals) (l : NonnegativeReals) : hProp
  := hProppair (∀ eps : NonnegativeReals,
                   0 < eps ->
                   hexists
                     (λ N : nat,
                            ∀ n : nat, N ≤ n -> u n < l + eps × l < u n + eps))
               (impred_isaprop _ (λ _, isapropimpl _ _ (pr2 _))).
Lemma max_le_l : ∀ n m : nat, (n <= Nat.max n m)%nat.
Admitted.
Lemma max_le_r : ∀ n m : nat, (m <= Nat.max n m)%nat.
Admitted.

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
  specialize (Hn (Nat.max N M) (max_le_l _ _)).
  specialize (Hm (Nat.max N M) (max_le_r _ _)).
  apply (isirrefl_Dcuts_lt_rel ((l + l') / 2)).
  apply istrans_Dcuts_lt_rel with (u (Nat.max N M)).
  - apply_pr2 (plusNonnegativeReals_ltcompat_l ((l' - l) / 2)).
    rewrite <- isdistr_Dcuts_half_plus.
    rewrite (iscomm_plusNonnegativeReals l), isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals l).
    rewrite <- (minusNonnegativeReals_plus_r (l' - l) l' l), isdistr_Dcuts_half_plus, <- double_Dcuts_half.
    exact (pr2 Hm).
    now apply Dcuts_lt_le_rel.
    reflexivity.
  - rewrite (minusNonnegativeReals_plus_r (l' - l) l' l), (iscomm_plusNonnegativeReals _ l), <- isassoc_plusNonnegativeReals, !isdistr_Dcuts_half_plus, <-double_Dcuts_half.
    exact (pr1 Hn).
    now apply Dcuts_lt_le_rel.
    reflexivity.
Qed.
Lemma is_lim_seq_unique (u : nat -> NonnegativeReals) (l l' : NonnegativeReals) :
  is_lim_seq u l -> is_lim_seq u l' -> l = l'.
Proof.
  intros u l l' Hl Hl'.
  apply notapNonnegativeReals_eq.
  unfold neg ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros [ | ].
  - now apply (is_lim_seq_unique_aux u).
  - now apply (is_lim_seq_unique_aux u).
Qed.
Definition ex_lim_seq  (u : nat -> NonnegativeReals) : hProp.
Proof.
  intro u.
  apply (hProppair (Σ l : NonnegativeReals, is_lim_seq u l)).
  intros Hl Hl'.
  apply (iscontrweqf (X := (pr1 Hl = pr1 Hl'))).
  now apply invweq, total2_paths_hProp_equiv.
  rewrite (is_lim_seq_unique _ _ _ (pr2 Hl) (pr2 Hl')).
  apply iscontrloopsifisaset.
  apply pr2.
Defined.
Definition Lim_seq (u : nat -> NonnegativeReals) (Lu : ex_lim_seq u) : NonnegativeReals
  := pr1 Lu.

Lemma Cauchy_seq_impl_ex_lim_seq (u : nat -> NonnegativeReals) :
  Cauchy_seq u -> ex_lim_seq u.
Proof.
  intros u Cu.
  set (E := λ n : nat, (λ x : NonnegativeReals, hexists (λ m : nat, x = u m × (n <= m)%nat))).
  set (v := λ n : nat, lubNonnegativeReals (E n)).
  assert (E_cauchy : ∀ n : nat, (∀ c : NonnegativeReals,
                                    0 < c ->
                                    isUpperBound (X := eo_Dcuts) (E n) c
                                    ∨ hexists (λ x : Dcuts, E n x × isUpperBound (X := eo_Dcuts) (E n) (x + c)))).
  { intros n c Hc0.
    generalize (Cu c Hc0) ; clear.

    apply hinhfun ; intros (N,Hu).
    right.
    Search pr1.
    case (natgthorleh N n) ; intro Hind.
    revert u Hu E.
    - induction N ; intros u Hu E.
      + now apply fromempty, (negnatgth0n n).
      + apply natgthsntogeh, natgehchoice in Hind.
        case Hind ; clear Hind ; intro Hind.
        * set (u' := λ m : nat, match nat_eq_or_neq N m with
                                | ii1 _ => u (S N)
                                | ii2 _ => u m
                                end).
          assert (Hu' : ∀ n m : nat, N ≤ n -> N ≤ m -> u' n < u' m + c × u' m < u' n + c).
          { clear -Hu.
            intros n m Hn Hm.
            unfold u' ;
            case nat_eq_or_neq ; intros Hn' ;
            case nat_eq_or_neq ; intros Hm' ;
            apply Hu.
            - now apply isreflnatleh.
            - now apply isreflnatleh.
            - now apply isreflnatleh.
            - now apply natlthtolehsn, natleh_neq.
            - now apply natlthtolehsn, natleh_neq.
            - now apply isreflnatleh.
            - now apply natlthtolehsn, natleh_neq.
            - now apply natlthtolehsn, natleh_neq.
          }
          generalize (IHN Hind u' Hu').
          apply hinhuniv ; intros (um,(Eum,Hum)).
          revert Eum ; apply hinhfun ; intros (m,(->,Hmn)).
          exists (maxNonnegativeReals (u N) (u' m)) ; split.
          admit.
          intros x.
          apply hinhuniv ; intros (k,(->,Hkn)).
          admit.
        * admit.
    - admit.
  }
Admitted.

(** ** Opacify *)

Global Opaque NonnegativeReals.
Global Opaque leNonnegativeReals ltNonnegativeReals.
Global Opaque geNonnegativeReals gtNonnegativeReals.
Global Opaque lubNonnegativeReals.
Global Opaque minusNonnegativeReals maxNonnegativeReals halfNonnegativeReals.

(* End of the file Dcuts.v *)
