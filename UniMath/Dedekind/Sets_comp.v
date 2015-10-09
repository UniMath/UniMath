(** * Additionnals theorems for Sets.v *)

(** Previous theorems about hSet and order *)

Require Export UniMath.Foundations.Sets
               UniMath.Ktheory.Sets
               UniMath.Ktheory.QuotientSet.

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
  intros X R L is.
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
