(** * Additionals theorems and definitions *)

(** ** for Sets.v *)

Require Export UniMath.Foundations.Sets.

(** *** Partiel Order *)

Definition isPartialOrder {X : UU} := ispo (X := X).
Definition PartialOrder := po.
Definition pairPartialOrder {X : UU} (R : hrel X) (is : isPartialOrder R) : PartialOrder X :=
  popair R is.
Definition pr1PartialOrder {X : UU} (R : PartialOrder X) : hrel X := carrierofpo X R.
Coercion  pr1PartialOrder : PartialOrder >-> hrel.

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

(** *** Complete Ordered Space *)

Definition isUpperBound {X : UU} (le : PartialOrder X) (E : X -> hProp) (ub : X) :=
  forall x : X, E x -> le x ub.
Definition isSmallerThanUpperBounds {X : UU} (le : PartialOrder X) (E : X -> hProp) (lub : X) :=
  forall ub : X, isUpperBound le E ub -> le lub ub.

Definition isLeastUpperBound {X : UU} (le : PartialOrder X) (E : X -> hProp) (lub : X) :=
  dirprod (isUpperBound le E lub) (isSmallerThanUpperBounds le E lub).
Definition LeastUpperBound {X : UU} (le : PartialOrder X) (E : X -> hProp) :=
  total2 (isLeastUpperBound le E).
Definition pairLeastUpperBound {X : UU} (le : PartialOrder X) (E : X -> hProp) (lub : X)
           (is : isLeastUpperBound le E lub) : LeastUpperBound le E :=
  tpair (isLeastUpperBound le E) lub is.
Definition pr1LeastUpperBound {X : UU} {le : PartialOrder X} {E : X -> hProp} :
  LeastUpperBound le E -> X := pr1.

Definition isCompletePartialOrder {X : UU} (le : PartialOrder X) :=
  forall E : X -> hProp,
    hexists (isUpperBound le E) -> hexists E -> LeastUpperBound le E.
Definition CompletePartialOrder (X : UU) :=
  total2 (fun le : PartialOrder X => isCompletePartialOrder le).
Definition pr1CompletePartialOrder {X : UU} : CompletePartialOrder X -> PartialOrder X := pr1.
Coercion pr1CompletePartialOrder : CompletePartialOrder >-> PartialOrder.

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.RationalNumbers.

Open Scope hq_scope.

Lemma hq0lehandplus:
  forall n m : hq,
    hqleh 0 n -> hqleh 0 m -> hqleh 0 (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.

Close Scope hq_scope.
