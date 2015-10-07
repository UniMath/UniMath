(** * Additionals theorems and definitions *)

(** ** for Sets.v *)

Require Export UniMath.Foundations.Sets.

(** *** Strict Partial Order *)

Definition isStrictPartialOrder {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition StrictPartialOrder (X : UU) := total2 (fun R : hrel X => isStrictPartialOrder R ).
Definition pairStrictPartialOrder {X : UU} (R : hrel X) (is : isStrictPartialOrder R) : StrictPartialOrder X :=
  tpair (fun R : hrel X => isStrictPartialOrder R ) R is.
Definition pr1StrictPartialOrder {X : UU} : StrictPartialOrder X -> hrel X := pr1.
Coercion  pr1StrictPartialOrder : StrictPartialOrder >-> hrel.

Definition isStrictPartialOrder_quotrel {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrictPartialOrder L -> isStrictPartialOrder (quotrel is).
Proof.
  intros (Htrans,Hirrefl).
  split.
  now apply istransquotrel.
  now apply isirreflquotrel.
Defined.

(** *** Effectively Ordered *)

Definition isEffectiveOrder {X : UU} (le : po X) (gt : StrictPartialOrder X) :=
  forall x y : X, le x y -> gt x y -> empty.
Definition EffectiveOrder (X : UU) := total2 (fun legt : po X * StrictPartialOrder X => isEffectiveOrder (fst legt) (snd legt)).
Definition pairEffectiveOrder {X : UU} (le : po X) (gt : StrictPartialOrder X) (is : isEffectiveOrder le gt) : EffectiveOrder X :=
  tpair _ (le,gt) is.
Definition leEffectiveOrder {X : UU} (R : EffectiveOrder X) : hrel X :=
  match R with
  | tpair _ (le,_) _ => le
  end.
Definition geEffectiveOrder {X : UU} (R : EffectiveOrder X) : hrel X :=
  match R with
  | tpair _ (le,_) _ => fun x y => le y x
  end.
Definition gtEffectiveOrder {X : UU} (R : EffectiveOrder X) : hrel X :=
  match R with
  | tpair _ (_,gt) _ => gt
  end.
Definition ltEffectiveOrder {X : UU} (R : EffectiveOrder X) : hrel X :=
  match R with
  | tpair _ (_,gt) _ => fun x y => gt y x
  end.

Notation "x <= y" := (leEffectiveOrder x y) : eo_scope.
Notation "x >= y" := (geEffectiveOrder x y) : eo_scope.
Notation "x < y" := (ltEffectiveOrder x y) : eo_scope.
Notation "x > y" := (gtEffectiveOrder x y) : eo_scope.

(** *** Complete Ordered Space *)

Definition lePoset {X : Poset} : hrel X :=
  match X with
  | tpair _ _ le => le
  end.
Definition subset (X : hSet) : hSet := hSetpair _ (isasethsubtypes X).

Definition isUpperBound {X : UU} (le : po X) (E : X -> hProp) (ub : X) :=
  forall x : X, E x -> le x ub.
Definition isSmallerThanUpperBounds {X : UU} le E (lub : X) :=
  forall ub : X, isUpperBound le E ub -> le lub ub.

Definition isLeastUpperBound {X : UU} le E (lub : X) :=
  dirprod (isUpperBound le E lub) (isSmallerThanUpperBounds le E lub).
Definition LeastUpperBound {X : UU} (le : po X) E :=
  total2 (isLeastUpperBound le E).
Definition pairLeastUpperBound {X : UU} le E (lub : X)
           (is : isLeastUpperBound le E lub) : LeastUpperBound le E :=
  tpair (isLeastUpperBound le E) lub is.
Definition pr1LeastUpperBound {X : UU} {le : po X} {E : X -> hProp} :
  LeastUpperBound le E -> X := pr1.

Definition isCompleteOrder {X : UU} (le : po X) :=
  forall E,
    hexists (isUpperBound le E) -> hexists E -> LeastUpperBound le E.
Definition CompleteOrder (X : UU) :=
  total2 (fun le : po X => isCompleteOrder le).
Definition pr1CompleteOrder {X : UU} : CompleteOrder X -> hrel X := pr1.
Coercion pr1CompleteOrder : CompleteOrder >-> hrel.

Definition isCompleteSet (X : UU) := CompleteOrder X.
Definition CompleteSet := total2 (fun X : UU => isCompleteSet X).
Definition pr1CompleteSet : CompleteSet -> UU := pr1.
Coercion pr1CompleteSet : CompleteSet >-> UU.

(** ** For Fields *)

Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

Definition fld_to_addmonoid : fld -> monoid.
Proof.
  intro.
  destruct X as (t,_).
  destruct t.
  exists (setwithbinop1 t).
  now apply p.
Defined.
Definition fld_to_multmonoid : fld -> monoid.
Proof.
  intro.
  destruct X as (t,_).
  destruct t.
  exists (setwithbinop2 t).
  destruct p.
  destruct t0.
  destruct t0.
  apply p1.
Defined.

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.RationalNumbers.

Open Scope hq_scope.

Notation "x <= y" := (hqleh x y) : hq_scope.
Notation "x >= y" := (hqgeh x y) : hq_scope.
Notation "x < y" := (hqlth x y) : hq_scope.
Notation "x > y" := (hqgth x y) : hq_scope.
Notation "/ x" := (hqmultinv x) : hq_scope.
Notation "x / y" := (hqdiv x y) : hq_scope.
Notation "2" := (hztohq (nattohz 2)) : hq_scope.

Lemma hztohq_0 :
  hztohq 0%hz = 0.
Proof.
  now apply isunital1funtofldfrac.
Qed.
Lemma hztohq_1 :
  hztohq 1%hz = 1.
Proof.
  now apply isunital2funtofldfrac.
Qed.

Lemma hq2eq1plus1 :
  2 = 1 + 1.
Proof.
  rewrite <- hztohq_1, <- nattohzand1.
  now rewrite <- hztohqandplus, <- nattohzandplus.
Qed.

Lemma hq2_gt0 : 2 > 0.
Proof.
  rewrite <- hztohq_0, <- nattohzand0.
  now apply hztohqandgth, nattohzandgth.
Qed.
Lemma hq1_gt0 : 1 > 0.
Proof.
  rewrite <- hztohq_0, <- hztohq_1.
  rewrite <- nattohzand1, <- nattohzand0.
  now apply hztohqandgth, nattohzandgth.
Qed.
Lemma hqgth_hqneq :
  forall x y : hq, x > y -> hqneq x y.
Proof.
  intros x y Hlt Heq.
  rewrite Heq in Hlt.
  now apply isirreflhqgth with y.
Qed.

Lemma hqldistr :
  forall x y z, x * (y + z) = x * y + x * z.
Proof.
  intros x y z.
  now apply rngldistr.
Qed.

Lemma hqmult2r :
  forall x : hq, x * 2 = x + x.
Proof.
  intros x.
  now rewrite hq2eq1plus1, hqldistr, (hqmultr1 x).
Qed.

Lemma hqplusdiv2 : forall x : hq, x = (x + x) / 2.
  intros x.
  apply hqmultrcan with 2.
  now apply hqgth_hqneq, hq2_gt0.
  unfold hqdiv.
  rewrite hqmultassoc.
  rewrite (hqislinvmultinv 2).
  2: now apply hqgth_hqneq, hq2_gt0.
  rewrite (hqmultr1 (x + x)).
  apply hqmult2r.
Qed.

Lemma hqlth_between :
  forall x y : hq, x < y -> total2 (fun z => dirprod (x < z) (z < y)).
Proof.
  assert (H0 : / 2 > 0).
  { apply hqgthandmultlinv with 2.
    apply hq2_gt0.
    rewrite hqisrinvmultinv, hqmultx0.
    now apply hq1_gt0.
    now apply hqgth_hqneq, hq2_gt0.
  }
  intros x y Hlt.
  exists ((x + y) / 2).
  split.
  - pattern x at 1.
    rewrite (hqplusdiv2 x).
    unfold hqdiv.
    apply (hqlthandmultr _ _ (/ 2)).
    exact H0.
    now apply (hqlthandplusl _ _ x Hlt).
  - pattern y at 2.
    rewrite (hqplusdiv2 y).
    unfold hqdiv.
    apply (hqlthandmultr _ _ (/ 2)).
    exact H0.
    now apply (hqlthandplusr _ _ y Hlt).
Qed.

Lemma hq0lehandplus:
  forall n m : hq,
    0 <= n -> 0 <= m -> 0 <= (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.

Close Scope hq_scope.
