(** * Additionals theorems and definitions *)

(** ** for Sets.v *)

Require Export UniMath.Foundations.Sets.

(** *** Strict Partial Order *)

Definition isStrictPartialOrder {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition StrictPartialOrder (X : UU) := total2 (fun R : hrel X => isStrictPartialOrder R ).
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

Definition isub {X : UU} (le : hrel X) (E : X -> hProp) (ub : X) :=
  forall x : X, E x -> le x ub.
Definition islbub {X : UU} (le : hrel X) (E : X -> hProp) (lub : X) :=
  forall ub : X, isub le E ub -> le lub ub.
Definition islub {X : UU} (le : hrel X) (E : X -> hProp) (lub : X) :=
  dirprod (isub le E lub) (islbub le E lub).

Definition lub {X : UU} (le : hrel X) (E : X -> hProp) :=
  total2 (islub le E).

Definition iscompleterel {X : UU} (le : hrel X) :=
  forall E : X -> hProp,
    hexists (isub le E) ->
    hexists E -> lub le E.
Definition completerel (X : UU) :=
  total2 (fun le : hrel X => iscompleterel le).
Definition pr1completerel {X : UU} : completerel X -> hrel X := pr1.
Coercion pr1completerel : completerel >-> hrel.

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
