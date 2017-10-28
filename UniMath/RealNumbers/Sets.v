(** * Additionnals theorems for Sets.v *)

(** Previous theorems about hSet and order *)

Require Import UniMath.MoreFoundations.Tactics.

Require Export UniMath.Foundations.Sets
               UniMath.Ktheory.QuotientSet.
Require Import UniMath.Algebra.BinaryOperations
               UniMath.Algebra.Apartness
               UniMath.Algebra.Lattice.

Unset Automatic Introduction.

(** ** Subsets *)

Lemma isaset_hsubtype {X : hSet} (Hsub : hsubtype X) : isaset (carrier Hsub).
Proof.
  intros X Hsub.
  apply (isasetsubset pr1 (pr2 X) (isinclpr1 (λ x : X, Hsub x) (λ x : X, pr2 (Hsub x)))).
Qed.
Definition subset {X : hSet} (Hsub : hsubtype X) : hSet :=
  hSetpair (carrier Hsub) (isaset_hsubtype Hsub).
Definition makeSubset {X : hSet} {Hsub : hsubtype X} (x : X) (Hx : Hsub x) : subset Hsub :=
  x,, Hx.

(** ** Additional definitions *)

Definition unop (X : UU) := X → X.

Definition islinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X) :=
  ∏ (x : X) (Hx : exinv x), op (inv (x ,, Hx)) x = x1.
Definition isrinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X) :=
  ∏ (x : X) (Hx : exinv x), op x (inv (x ,, Hx)) = x1.
Definition isinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtype X) (inv : subset exinv -> X)  :=
  islinv' x1 op exinv inv × isrinv' x1 op exinv inv.

(** ** Properties of [po] *)

Section po_pty.

Context {X : UU}.
Context (R : po X).

Definition istrans_po : istrans R :=
  pr1 (pr2 R).
Definition isrefl_po : isrefl R :=
  pr2 (pr2 R).

End po_pty.

(** ** Reverse orderse *)
(** or how easily define ge x y := le x y *)

Definition hrel_reverse {X : UU} (l : hrel X) := λ x y, l y x.

Lemma istrans_reverse {X : UU} (l : hrel X) :
  istrans l → istrans (hrel_reverse l).
Proof.
  intros X l Hl x y z Hxy Hyz.
  now apply (Hl z y x).
Qed.

Lemma isrefl_reverse {X : UU} (l : hrel X) :
  isrefl l → isrefl (hrel_reverse l).
Proof.
  intros X l Hl x.
  now apply Hl.
Qed.

Lemma ispreorder_reverse {X : UU} (l : hrel X) :
  ispreorder l → ispreorder (hrel_reverse l).
Proof.
  intros X l H.
  split.
  now apply istrans_reverse, (pr1 H).
  now apply isrefl_reverse, (pr2 H).
Qed.
Definition po_reverse {X : UU} (l : po X) :=
  popair (hrel_reverse l) (ispreorder_reverse l (pr2 l)).
Lemma po_reverse_correct {X : UU} (l : po X) :
  ∏ x y : X, po_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma issymm_reverse {X : UU} (l : hrel X) :
  issymm l → issymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma iseqrel_reverse {X : UU} (l : hrel X) :
  iseqrel l → iseqrel (hrel_reverse l).
Proof.
  intros X l H.
  split.
  now apply ispreorder_reverse, (pr1 H).
  now apply issymm_reverse, (pr2 H).
Qed.
Definition eqrel_reverse {X : UU} (l : eqrel X) :=
  eqrelpair (hrel_reverse l) (iseqrel_reverse l (pr2 l)).
Lemma eqrel_reverse_correct {X : UU} (l : eqrel X) :
  ∏ x y : X, eqrel_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma isirrefl_reverse {X : UU} (l : hrel X) :
  isirrefl l → isirrefl (hrel_reverse l).
Proof.
  intros X l Hl x.
  now apply Hl.
Qed.
Lemma iscotrans_reverse {X : UU} (l : hrel X) :
  iscotrans l -> iscotrans (hrel_reverse l).
Proof.
  intros X l Hl x y z H.
  now apply islogeqcommhdisj, Hl.
Qed.

Lemma isStrongOrder_reverse {X : UU} (l : hrel X) :
  isStrongOrder l → isStrongOrder (hrel_reverse l).
Proof.
  intros X l H.
  mkStrongOrder.
  - apply istrans_reverse, (istrans_StrongOrder (_,,H)).
  - apply iscotrans_reverse,(iscotrans_StrongOrder (_,,H)).
  - apply isirrefl_reverse, (isirrefl_StrongOrder (_,,H)).
Qed.
Definition StrongOrder_reverse {X : UU} (l : StrongOrder X) :=
  pairStrongOrder (hrel_reverse l) (isStrongOrder_reverse l (pr2 l)).
Lemma StrongOrder_reverse_correct {X : UU} (l : StrongOrder X) :
  ∏ x y : X, StrongOrder_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma isasymm_reverse {X : UU} (l : hrel X) :
  isasymm l → isasymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma iscoasymm_reverse {X : UU} (l : hrel X) :
  iscoasymm l → iscoasymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma istotal_reverse {X : UU} (l : hrel X) :
  istotal l → istotal (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

(** ** Effectively Ordered *)
(** An alternative of total orders *)

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
  popair (pr1 R) (pr1 (pr1 (pr2 (pr2 R)))).
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
  pairStrongOrder (pr1 (pr2 R)) (pr2 (pr1 (pr2 (pr2 R)))).
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

Delimit Scope eo_scope with eo.

Notation "x <= y" := (EOle_rel x y) : eo_scope.
Notation "x >= y" := (EOge_rel x y) : eo_scope.
Notation "x < y" := (EOlt_rel x y) : eo_scope.
Notation "x > y" := (EOgt_rel x y) : eo_scope.

Section eo_pty.

Context {X : EffectivelyOrderedSet}.

Open Scope eo_scope.

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
  := isirrefl_StrongOrder EOgt.
Definition istrans_EOgt:
  ∏ x y z : X, x > y -> y > z -> x > z
  := istrans_StrongOrder EOgt.

Definition isirrefl_EOlt:
  ∏ x : X, ¬ (x < x)
  := isirrefl_StrongOrder EOlt.
Definition istrans_EOlt:
  ∏ x y z : X, x < y -> y < z -> x < z
  := istrans_StrongOrder EOlt.

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
  intros E H x y.
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
  intros E H x y.
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
