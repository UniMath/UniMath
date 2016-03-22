(** * Additionnals theorems for Sets.v *)

(** Previous theorems about hSet and order *)

Require Export UniMath.Foundations.Basics.Sets
               UniMath.Ktheory.QuotientSet.
Require Import UniMath.Foundations.Algebra.BinaryOperations.

(** ** Subsets *)

Lemma isaset_subtype {X : hSet} (Hsub : subtype X) : isaset (carrier Hsub).
Proof.
  intros.
  apply (isasetsubset pr1 (pr2 X) (isinclpr1 (λ x : X, Hsub x) (λ x : X, pr2 (Hsub x)))).
Qed.
Definition subset {X : hSet} (Hsub : subtype X) : hSet :=
  hSetpair (carrier Hsub) (isaset_subtype Hsub).
Definition makeSubset {X : hSet} {Hsub : subtype X} (x : X) (Hx : Hsub x) : subset Hsub :=
  x,, Hx.

(** ** Additional definitions *)

Definition unop (X : UU) := X -> X.

Definition islinv' {X : hSet} (x1 : X) (op : binop X) (exinv : subtype X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op (inv (x ,, Hx)) x = x1.
Definition isrinv' {X : hSet} (x1 : X) (op : binop X) (exinv : subtype X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op x (inv (x ,, Hx)) = x1.
Definition isinv' {X : hSet} (x1 : X) (op : binop X) (exinv : subtype X) (inv : subset exinv -> X)  :=
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

(** ** Strong Order *)

Definition isStrongOrder {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition StrongOrder (X : UU) := total2 (fun R : hrel X => isStrongOrder R ).
Definition pairStrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  tpair (fun R : hrel X => isStrongOrder R ) R is.
Definition pr1StrongOrder {X : UU} : StrongOrder X -> hrel X := pr1.
Coercion  pr1StrongOrder : StrongOrder >-> hrel.

Section so_pty.

Context {X : UU}.
Context (R : StrongOrder X).

Definition istrans_StrongOrder : istrans R :=
  pr1 (pr2 R).
Definition isirrefl_StrongOrder : isirrefl R :=
  pr2 (pr2 R).

End so_pty.

Definition isStrongOrder_quotrel {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L -> isStrongOrder (quotrel is).
Proof.
  intros X R L is.
  intros (Htrans,Hirrefl).
  split.
  now apply istransquotrel.
  now apply isirreflquotrel.
Defined.

(** ** Reverse orderse *)
(** or how easily define ge x y := le x y *)

Definition hrel_reverse {X : UU} (l : hrel X) := fun x y => l y x.

Lemma istrans_reverse {X : UU} (l : hrel X) :
  istrans l -> istrans (hrel_reverse l).
Proof.
  intros X l Hl x y z Hxy Hyz.
  now apply (Hl z y x).
Qed.

Lemma isrefl_reverse {X : UU} (l : hrel X) :
  isrefl l -> isrefl (hrel_reverse l).
Proof.
  intros X l Hl x.
  now apply Hl.
Qed.

Lemma ispreorder_reverse {X : UU} (l : hrel X) :
  ispreorder l -> ispreorder (hrel_reverse l).
Proof.
  intros X l (Ht,Hr).
  split.
  now apply istrans_reverse.
  now apply isrefl_reverse.
Qed.
Definition po_reverse {X : UU} (l : po X) :=
  popair (hrel_reverse l) (ispreorder_reverse l (pr2 l)).
Lemma po_reverse_correct {X : UU} (l : po X) :
  forall x y : X, po_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma issymm_reverse {X : UU} (l : hrel X) :
  issymm l -> issymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma iseqrel_reverse {X : UU} (l : hrel X) :
  iseqrel l -> iseqrel (hrel_reverse l).
Proof.
  intros X l (Hpo,Hs).
  split.
  now apply ispreorder_reverse.
  now apply issymm_reverse.
Qed.
Definition eqrel_reverse {X : UU} (l : eqrel X) :=
  eqrelpair (hrel_reverse l) (iseqrel_reverse l (pr2 l)).
Lemma eqrel_reverse_correct {X : UU} (l : eqrel X) :
  forall x y : X, eqrel_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma isirrefl_reverse {X : UU} (l : hrel X) :
  isirrefl l -> isirrefl (hrel_reverse l).
Proof.
  intros X l Hl x.
  now apply Hl.
Qed.

Lemma isStrongOrder_reverse {X : UU} (l : hrel X) :
  isStrongOrder l -> isStrongOrder (hrel_reverse l).
Proof.
  intros X l (Ht,Hir).
  split.
  now apply istrans_reverse.
  now apply isirrefl_reverse.
Qed.
Definition StrongOrder_reverse {X : UU} (l : StrongOrder X) :=
  pairStrongOrder (hrel_reverse l) (isStrongOrder_reverse l (pr2 l)).
Lemma StrongOrder_reverse_correct {X : UU} (l : StrongOrder X) :
  forall x y : X, StrongOrder_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.

Lemma isasymm_reverse {X : UU} (l : hrel X) :
  isasymm l -> isasymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma iscoasymm_reverse {X : UU} (l : hrel X) :
  iscoasymm l -> iscoasymm (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma istotal_reverse {X : UU} (l : hrel X) :
  istotal l -> istotal (hrel_reverse l).
Proof.
  intros X l Hl x y.
  now apply Hl.
Qed.

Lemma iscotrans_reverse {X : UU} (l : hrel X) :
  iscotrans l -> iscotrans (hrel_reverse l).
Proof.
  intros X l Hl x y z H.
  apply islogeqcommhdisj.
  now apply Hl.
Qed.

(** ** Effectively Ordered *)
(** An alternative of total orders *)

Definition isEffectiveOrder {X : UU} (le lt : hrel X) :=
  dirprod ((ispreorder le) × (isStrongOrder lt))
          ((forall x y : X, lt x y -> le x y)
             × (forall x y : X, (¬ lt x y) <-> (le y x))
             × (forall x y z : X, lt x y -> le y z -> lt x z)
             × (forall x y z : X, le x y -> lt y z -> lt x z)).
Definition EffectiveOrder (X : UU) :=
  Σ lelt : hrel X * hrel X, isEffectiveOrder (fst lelt) (snd lelt).
Definition pairEffectiveOrder {X : UU} (le lt : hrel X) (is : isEffectiveOrder le lt) : EffectiveOrder X :=
  tpair _ (le,lt) is.

Definition EffectivelyOrderedSet :=
  Σ X : hSet, EffectiveOrder X.
Definition pairEffectivelyOrderedSet {X : hSet} (is : EffectiveOrder X) : EffectivelyOrderedSet
  := tpair _ X is.
Definition pr1EffectivelyOrderedSet : EffectivelyOrderedSet -> hSet := pr1.
Coercion pr1EffectivelyOrderedSet : EffectivelyOrderedSet >-> hSet.

Definition EOle {X : EffectivelyOrderedSet} : po X :=
  let R := pr2 X in
  popair (fst (pr1 R)) (pr1 (pr1 (pr2 R))).
Definition EOle_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOle.
Arguments EOle_rel {!X} x y: simpl never.
Definition EOge {X : EffectivelyOrderedSet} : po X :=
  po_reverse (@EOle X).
Definition EOge_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOge.
Arguments EOge_rel {!X} x y: simpl never.

Definition EOlt {X : EffectivelyOrderedSet} : StrongOrder (pr1 X) :=
  let R := pr2 X in
  pairStrongOrder (snd (pr1 R)) (pr2 (pr1 (pr2 R))).
Definition EOlt_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOlt.
Arguments EOlt_rel {!X} x y: simpl never.
Definition EOgt {X : EffectivelyOrderedSet} : StrongOrder (pr1 X) :=
  StrongOrder_reverse (@EOlt X).
Definition EOgt_rel {X : EffectivelyOrderedSet} : hrel X :=
  pr1 EOgt.
Arguments EOgt_rel {!X} x y: simpl never.

Definition PreorderedSetEffectiveOrder (X : EffectivelyOrderedSet) : PreorderedSet :=
  PreorderedSetPair _ (@EOle X).
Coercion PreorderedSetEffectiveOrder : EffectivelyOrderedSet >-> PreorderedSet.

Delimit Scope eo_scope with eo.

Notation "x <= y" := (EOle_rel x y) : eo_scope.
Notation "x >= y" := (EOge_rel x y) : eo_scope.
Notation "x < y" := (EOlt_rel x y) : eo_scope.
Notation "x > y" := (EOgt_rel x y) : eo_scope.

Section eo_pty.

Context {X : EffectivelyOrderedSet}.

Open Scope eo_scope.

Definition not_EOlt_le :
  ∀ x y : X, (¬ (x < y)) <-> (y <= x)
  := (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Lemma EOge_le:
  ∀ x y : X, (x >= y) <-> (y <= x).
Proof.
  now split.
Qed.
Lemma EOgt_lt:
  ∀ x y : X, (x > y) <-> (y < x).
Proof.
  now split.
Qed.

Definition EOlt_le :
  forall x y : X, x < y -> x <= y
  := (pr1 (pr2 (pr2 (pr2 X)))).

Definition isrefl_EOle:
  forall x : X, x <= x
  := isrefl_po EOle.
Definition istrans_EOle:
  ∀ x y z : X, x <= y -> y <= z -> x <= z
  := istrans_po EOle.

Definition isirrefl_EOlt:
  forall x : X, ¬ (x < x)
  := isirrefl_StrongOrder EOlt.
Definition istrans_EOlt:
  ∀ x y z : X, x < y -> y < z -> x < z
  := istrans_StrongOrder EOlt.

Definition istrans_EOlt_le:
  ∀ x y z : X, x < y -> y <= z -> x < z
  := (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Definition istrans_EOle_lt:
  ∀ x y z : X, x <= y -> y < z -> x < z
  := (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).

Lemma EOlt_noteq :
  ∀ x y : X, x < y -> x != y.
Proof.
  intros x y Hlt Heq.
  rewrite Heq in Hlt.
  now apply isirrefl_EOlt in Hlt.
Qed.
Lemma EOgt_noteq :
  ∀ x y : X, x > y -> x != y.
Proof.
  intros x y Hgt Heq.
  rewrite Heq in Hgt.
  now apply isirrefl_EOlt in Hgt.
Qed.

Close Scope eo_scope.

End eo_pty.

(** ** Complete Ordered Space *)

Section LeastUpperBound.

Context {X : PreorderedSet}.
Local Notation "x <= y" := (pr1 (pr2 X) x y).

Definition isUpperBound (E : subtype X) (ub : X) : UU :=
  forall x : X, E x -> x <= ub.
Definition isSmallerThanUpperBounds (E : subtype X) (lub : X) : UU :=
  forall ub : X, isUpperBound E ub -> lub <= ub.

Definition isLeastUpperBound (E : subtype X) (lub : X) : UU :=
  dirprod (isUpperBound E lub) (isSmallerThanUpperBounds E lub).
Definition LeastUpperBound (E : subtype X) : UU :=
  total2 (isLeastUpperBound E).
Definition pairLeastUpperBound (E : subtype X) (lub : X)
           (is : isLeastUpperBound E lub) : LeastUpperBound E :=
  tpair (isLeastUpperBound E) lub is.
Definition pr1LeastUpperBound {E : subtype X} :
  LeastUpperBound E -> X := pr1.

Lemma isapropLeastUpperBound (E : subtype X) (H : isantisymm (λ x y : X, x <= y)) :
  isaprop (LeastUpperBound E).
Proof.
  intros E H (x,Hx) (y,Hy).
  apply (iscontrweqf (X := x = y)).
  - apply invweq, subtypeInjectivity.
    intro t.
    apply isapropdirprod.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
  - assert (Heq : x = y).
    { apply H.
      now apply (pr2 Hx), (pr1 Hy).
      now apply (pr2 Hy), (pr1 Hx). }
    rewrite <- Heq.
    apply iscontrloopsifisaset.
    apply pr2.
Qed.

End LeastUpperBound.

Section GreatestLowerBound.

Context {X : PreorderedSet}.
Local Notation "x >= y" := (pr1 (pr2 X) y x).

Definition isLowerBound (E : subtype X) (ub : X) : UU :=
  forall x : X, E x -> x >= ub.
Definition isBiggerThanLowerBounds (E : subtype X) (lub : X) : UU :=
  forall ub : X, isLowerBound E ub -> lub >= ub.

Definition isGreatestLowerBound (E : subtype X) (lub : X) : UU :=
  dirprod (isLowerBound E lub) (isBiggerThanLowerBounds E lub).
Definition GreatestLowerBound (E : subtype X) : UU :=
  total2 (isGreatestLowerBound E).
Definition pairGreatestLowerBound (E : subtype X) (lub : X)
           (is : isGreatestLowerBound E lub) : GreatestLowerBound E :=
  tpair (isGreatestLowerBound E) lub is.
Definition pr1GreatestLowerBound {E : subtype X} :
  GreatestLowerBound E -> X := pr1.

Lemma isapropGreatestLowerBound (E : subtype X) (H : isantisymm (λ x y : X, x >= y)) :
  isaprop (GreatestLowerBound E).
Proof.
  intros E H (x,Hx) (y,Hy).
  apply (iscontrweqf (X := x = y)).
  - apply invweq, subtypeInjectivity.
    intro t.
    apply isapropdirprod.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply pr2.
  - assert (Heq : x = y).
    { apply H.
      now apply (pr2 Hx), (pr1 Hy).
      now apply (pr2 Hy), (pr1 Hx). }
    rewrite <- Heq.
    apply iscontrloopsifisaset.
    apply pr2.
Qed.

End GreatestLowerBound.

Definition isCompleteSpace (X : PreorderedSet) :=
  forall E : subtype X,
    hexists (isUpperBound E) -> hexists E -> LeastUpperBound E.
Definition CompleteSpace  :=
  total2 (fun X : PreorderedSet => isCompleteSpace X).
Definition pr1CompleteSpace : CompleteSpace -> UU := pr1.
Coercion pr1CompleteSpace : CompleteSpace >-> UU.
