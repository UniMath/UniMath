(** * Additional theorems for Sets.v *)

(** Previous theorems about hSet and order *)

Require Export UniMath.Foundations.Sets
               UniMath.MoreFoundations.QuotientSet.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Orders.

Require Import UniMath.Algebra.BinaryOperations
               UniMath.Algebra.Apartness
               UniMath.Algebra.Lattice.Lattice.

(** * Partially-defined inverse functions *)

Definition islinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X) :=
  ∏ (x : X) (Hx : exinv x), op (inv (x ,, Hx)) x = x1.
Definition isrinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X) :=
  ∏ (x : X) (Hx : exinv x), op x (inv (x ,, Hx)) = x1.
Definition isinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X)  :=
  islinv' x1 op exinv inv × isrinv' x1 op exinv inv.

(** * Effective Orders *)
(** An alternative to total orders *)

Definition isEffectiveOrder {X : UU} (le lt : hrel X) :=
  dirprod ((ispreorder le) × (isStrongOrder lt))
          ((∏ x y : X, (¬ lt x y) <-> (le y x))
          × (∏ x y z : X, lt x y -> le y z -> lt x z)
          × (∏ x y z : X, le x y -> lt y z -> lt x z)).
Definition EffectiveOrder (X : UU) :=
  ∑ le lt : hrel X, isEffectiveOrder le lt.
Definition pairEffectiveOrder {X : UU} (le lt : hrel X) (is : isEffectiveOrder le lt) : EffectiveOrder X :=
  (le,,lt,,is).

Definition EffectivelyOrderedSet :=
  ∑ X : hSet, EffectiveOrder X.
Definition pairEffectivelyOrderedSet {X : hSet} (is : EffectiveOrder X) : EffectivelyOrderedSet
  := tpair _ X is.
Definition pr1EffectivelyOrderedSet : EffectivelyOrderedSet → hSet := pr1.
Coercion pr1EffectivelyOrderedSet : EffectivelyOrderedSet >-> hSet.

Definition EOle {X : EffectivelyOrderedSet} : po X :=
  let R := pr2 X in
  make_po (pr1 R) (pr1 (pr1 (pr2 (pr2 R)))).
Definition EOle_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOle.
Arguments EOle_rel {X} x y: simpl never.
Definition EOge {X : EffectivelyOrderedSet} : po X :=
  po_reverse (@EOle X).
Definition EOge_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOge.
Arguments EOge_rel {X} x y: simpl never.

Definition EOlt {X : EffectivelyOrderedSet} : StrongOrder (pr1 X) :=
  let R := pr2 X in
  make_StrongOrder (pr1 (pr2 R)) (pr2 (pr1 (pr2 (pr2 R)))).
Definition EOlt_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOlt.
Arguments EOlt_rel {X} x y: simpl never.
Definition EOgt {X : EffectivelyOrderedSet} : StrongOrder (pr1 X) :=
  StrongOrder_reverse (@EOlt X).
Definition EOgt_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOgt.
Arguments EOgt_rel {X} x y: simpl never.

Definition PreorderedSetEffectiveOrder (X : EffectivelyOrderedSet) : PreorderedSet :=
  PreorderedSetPair _ (@EOle X).

Declare Scope eo_scope.
Delimit Scope eo_scope with eo.

Notation "x <= y" := (EOle_rel x y) : eo_scope.
Notation "x >= y" := (EOge_rel x y) : eo_scope.
Notation "x < y" := (EOlt_rel x y) : eo_scope.
Notation "x > y" := (EOgt_rel x y) : eo_scope.

Section eo_pty.

Context {X : EffectivelyOrderedSet}.

Local Open Scope eo_scope.

Lemma not_EOlt_le :
  ∏ x y : X, (¬ (x < y)) <-> (y <= x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma EOge_le:
  ∏ x y : X, (x >= y) <-> (y <= x).
Proof.
  now split.
Qed.
Lemma EOgt_lt:
  ∏ x y : X, (x > y) <-> (y < x).
Proof.
  now split.
Qed.

Definition isrefl_EOle:
  ∏ x : X, x <= x
  := isrefl_po EOle.
Definition istrans_EOle:
  ∏ x y z : X, x <= y -> y <= z -> x <= z
  := istrans_po EOle.

Definition isirrefl_EOgt:
  ∏ x : X, ¬ (x > x)
  := isirrefl_isStrongOrder EOgt.
Definition istrans_EOgt:
  ∏ x y z : X, x > y -> y > z -> x > z
  := istrans_isStrongOrder EOgt.

Definition isirrefl_EOlt:
  ∏ x : X, ¬ (x < x)
  := isirrefl_isStrongOrder EOlt.
Definition istrans_EOlt:
  ∏ x y z : X, x < y -> y < z -> x < z
  := istrans_isStrongOrder EOlt.

Lemma EOlt_le :
  ∏ x y : X, x < y -> x <= y.
Proof.
  intros x y Hxy.
  apply not_EOlt_le.
  intros H.
  refine (isirrefl_EOlt _ _).
  refine (istrans_EOlt _ _ _ _ _).
  exact Hxy.
  exact H.
Qed.

Lemma istrans_EOlt_le:
  ∏ x y z : X, x < y -> y <= z -> x < z.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.
Lemma istrans_EOle_lt:
  ∏ x y z : X, x <= y -> y < z -> x < z.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma EOlt_noteq :
  ∏ x y : X, x < y -> x != y.
Proof.
  intros x y Hgt Heq.
  rewrite Heq in Hgt.
  now apply isirrefl_EOgt in Hgt.
Qed.
Lemma EOgt_noteq :
  ∏ x y : X, x > y -> x != y.
Proof.
  intros x y Hgt Heq.
  rewrite Heq in Hgt.
  now apply isirrefl_EOgt in Hgt.
Qed.

Close Scope eo_scope.

End eo_pty.

(** ** Constructive Total Effective Order *)

Definition isConstructiveTotalEffectiveOrder {X : UU} (ap le lt : hrel X) :=
  istightap ap
  × isEffectiveOrder le lt
  × (isantisymm le)
  × (∏ x y : X, ap x y <-> (lt x y) ⨿ (lt y x)).
Definition ConstructiveTotalEffectiveOrder X :=
  ∑ ap lt le : hrel X, isConstructiveTotalEffectiveOrder ap lt le.
Definition ConstructiveTotalEffectivellyOrderedSet :=
  ∑ X : hSet, ConstructiveTotalEffectiveOrder X.

(** ** Complete Ordered Space *)

Section LeastUpperBound.

Context {X : PreorderedSet}.
Local Notation "x <= y" := (pr1 (pr2 X) x y).

Definition isUpperBound (E : hsubtype X) (ub : X) : UU :=
  ∏ x : X, E x -> x <= ub.
Definition isSmallerThanUpperBounds (E : hsubtype X) (lub : X) : UU :=
  ∏ ub : X, isUpperBound E ub -> lub <= ub.

Definition isLeastUpperBound (E : hsubtype X) (lub : X) : UU :=
  (isUpperBound E lub) × (isSmallerThanUpperBounds E lub).
Definition LeastUpperBound (E : hsubtype X) : UU :=
  ∑ lub : X, isLeastUpperBound E lub.
Definition pairLeastUpperBound (E : hsubtype X) (lub : X)
           (is : isLeastUpperBound E lub) : LeastUpperBound E :=
  tpair (isLeastUpperBound E) lub is.
Definition pr1LeastUpperBound {E : hsubtype X} :
  LeastUpperBound E → X := pr1.

Lemma isapropLeastUpperBound (E : hsubtype X) (H : isantisymm (λ x y : X, x <= y)) :
  isaprop (LeastUpperBound E).
Proof.
  intros x y.
  apply (iscontrweqf (X := (pr1 x) = (pr1 y))).
  - apply invweq, subtypeInjectivity.
    intro t.
    apply isapropdirprod.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
  - assert (Heq : (pr1 x) = (pr1 y)).
    { apply H.
      now apply (pr2 (pr2 x)), (pr1 (pr2 y)).
      now apply (pr2 (pr2 y)), (pr1 (pr2 x)). }
    rewrite <- Heq.
    apply iscontrloopsifisaset.
    apply pr2.
Qed.

End LeastUpperBound.

Section GreatestLowerBound.

Context {X : PreorderedSet}.
Local Notation "x >= y" := (pr1 (pr2 X) y x).

Definition isLowerBound (E : hsubtype X) (ub : X) : UU :=
  ∏ x : X, E x -> x >= ub.
Definition isBiggerThanLowerBounds (E : hsubtype X) (lub : X) : UU :=
  ∏ ub : X, isLowerBound E ub -> lub >= ub.

Definition isGreatestLowerBound (E : hsubtype X) (glb : X) : UU :=
  (isLowerBound E glb) × (isBiggerThanLowerBounds E glb).
Definition GreatestLowerBound (E : hsubtype X) : UU :=
  ∑ glb : X, isGreatestLowerBound E glb.
Definition pairGreatestLowerBound (E : hsubtype X) (glb : X)
           (is : isGreatestLowerBound E glb) : GreatestLowerBound E :=
  tpair (isGreatestLowerBound E) glb is.
Definition pr1GreatestLowerBound {E : hsubtype X} :
  GreatestLowerBound E → X := pr1.

Lemma isapropGreatestLowerBound (E : hsubtype X) (H : isantisymm (λ x y : X, x >= y)) :
  isaprop (GreatestLowerBound E).
Proof.
  intros x y.
  apply (iscontrweqf (X := (pr1 x) = (pr1 y))).
  - apply invweq, subtypeInjectivity.
    intro t.
    apply isapropdirprod.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
  - assert (Heq : (pr1 x) = (pr1 y)).
    { apply H.
      now apply (pr2 (pr2 x)), (pr1 (pr2 y)).
      now apply (pr2 (pr2 y)), (pr1 (pr2 x)). }
    rewrite <- Heq.
    apply iscontrloopsifisaset.
    apply pr2.
Qed.

End GreatestLowerBound.

Definition isCompleteSpace (X : PreorderedSet) :=
  ∏ E : hsubtype X,
    hexists (isUpperBound E) -> hexists E -> LeastUpperBound E.
Definition CompleteSpace  :=
  ∑ X : PreorderedSet, isCompleteSpace X.
Definition pr1CompleteSpace : CompleteSpace → UU := pr1.
Coercion pr1CompleteSpace : CompleteSpace >-> UU.
