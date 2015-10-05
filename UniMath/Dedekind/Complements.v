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

Definition isUpperBound {X : Poset} (E : subset X) (ub : X) :=
  forall x : X, E x -> lePoset x ub.
Definition isSmallerThanUpperBounds {X : Poset} (E : subset X) (lub : X) :=
  forall ub : X, isUpperBound E ub -> lePoset lub ub.

Definition isLeastUpperBound {X : Poset} (E : subset X) (lub : X) :=
  dirprod (isUpperBound E lub) (isSmallerThanUpperBounds E lub).
Definition LeastUpperBound {X : Poset} (E : subset X) :=
  total2 (isLeastUpperBound E).
Definition pairLeastUpperBound {X : Poset} (E : subset X) (lub : X)
           (is : isLeastUpperBound E lub) : LeastUpperBound E :=
  tpair (isLeastUpperBound E) lub is.
Definition pr1LeastUpperBound {X : Poset} {E : X -> hProp} :
  LeastUpperBound E -> X := pr1.

Definition isCompleteSet (X : Poset) :=
  forall E : subset X,
    hexists (isUpperBound E) -> hexists E -> LeastUpperBound E.
Definition CompleteSet :=
  total2 (fun X : Poset => isCompleteSet X).
Definition pr1CompletePartialOrder : CompleteSet -> Poset := pr1.
Coercion pr1CompletePartialOrder : CompleteSet >-> Poset.

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.RationalNumbers.

Open Scope hq_scope.

Notation "x <= y" := (hqleh x y) : hq_scope.
Notation "x >= y" := (hqgeh x y) : hq_scope.
Notation "x < y" := (hqlth x y) : hq_scope.
Notation "x > y" := (hqgth x y) : hq_scope.

Lemma hq0lehandplus:
  forall n m : hq,
    0 <= n -> 0 <= m -> 0 <= (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.

Close Scope hq_scope.
