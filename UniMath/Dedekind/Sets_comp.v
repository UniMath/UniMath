(** * Additionnals theorems for Sets.v *)

(** Previous theorems about hSet and order *)

Require Export UniMath.Foundations.Sets
               UniMath.Ktheory.Sets
               UniMath.Ktheory.QuotientSet.

(** ** Subsets *)

Definition subset (X : hSet) : hSet :=
  hSetpair _ (isasethsubtypes X).

(** ** Properties of [po] *)

Section po_pty.

Context {X : UU}.
Context (R : po X).

Definition istrans_po : istrans R :=
  pr1 (pr2 R).
Definition isrefl_po : isrefl R :=
  pr2 (pr2 R).

End po_pty.

(** ** Strict Partial Order *)

Definition isStrictPartialOrder {X : UU} (R : hrel X) := dirprod ( istrans R ) ( isirrefl R ).
Definition StrictPartialOrder (X : UU) := total2 (fun R : hrel X => isStrictPartialOrder R ).
Definition pairStrictPartialOrder {X : UU} (R : hrel X) (is : isStrictPartialOrder R) : StrictPartialOrder X :=
  tpair (fun R : hrel X => isStrictPartialOrder R ) R is.
Definition pr1StrictPartialOrder {X : UU} : StrictPartialOrder X -> hrel X := pr1.
Coercion  pr1StrictPartialOrder : StrictPartialOrder >-> hrel.

Section stpo_pty.

Context {X : UU}.
Context (R : StrictPartialOrder X).

Definition istrans_stpo : istrans R :=
  pr1 (pr2 R).
Definition isirrefl_stpo : isirrefl R :=
  pr2 (pr2 R).

End stpo_pty.

Definition isStrictPartialOrder_quotrel {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrictPartialOrder L -> isStrictPartialOrder (quotrel is).
Proof.
  intros X R L is.
  intros (Htrans,Hirrefl).
  split.
  now apply istransquotrel.
  now apply isirreflquotrel.
Defined.

(** ** Reverse orderse *)
(** or how have ge x y := le x y *)

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

Lemma ispo_reverse {X : UU} (l : hrel X) :
  ispo l -> ispo (hrel_reverse l).
Proof.
  intros X l (Ht,Hr).
  split.
  now apply istrans_reverse.
  now apply isrefl_reverse.
Qed.
Definition po_reverse {X : UU} (l : po X) :=
  popair (hrel_reverse l) (ispo_reverse l (pr2 l)).
Lemma po_reverse_correct {X : UU} (l : po X) :
  forall x y : X, po_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.
(* Opaque po_reverse. *)

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
  now apply ispo_reverse.
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
(* Opaque eqrel_reverse. *)

Lemma isirrefl_reverse {X : UU} (l : hrel X) :
  isirrefl l -> isirrefl (hrel_reverse l).
Proof.
  intros X l Hl x.
  now apply Hl.
Qed.

Lemma isStrictPartialOrder_reverse {X : UU} (l : hrel X) :
  isStrictPartialOrder l -> isStrictPartialOrder (hrel_reverse l).
Proof.
  intros X l (Ht,Hir).
  split.
  now apply istrans_reverse.
  now apply isirrefl_reverse.
Qed.
Definition StrictPartialOrder_reverse {X : UU} (l : StrictPartialOrder X) :=
  pairStrictPartialOrder (hrel_reverse l) (isStrictPartialOrder_reverse l (pr2 l)).
Lemma StrictPartialOrder_reverse_correct {X : UU} (l : StrictPartialOrder X) :
  forall x y : X, StrictPartialOrder_reverse l x y = l y x.
Proof.
  intros X l x y.
  now apply paths_refl.
Qed.
(* Opaque StrictPartialOrder_reverse. *)

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


(*  isdecrel
  isnegrel
  isantisymm
  isantisymmneg
  iscoantisymm
  hrellogeq*)
  
(** ** Effectively Ordered *)
(** An alternative of total orders *)

Definition isEffectiveOrder {X : UU} (le lt : hrel X) :=
  dirprod (dirprod (ispo le) (isStrictPartialOrder lt))
          (dirprod (forall x y : X, lt x y -> le x y)
                   (forall x y : X, le x y -> lt y x -> empty)).
Definition EffectiveOrder (X : UU) :=
  total2 (fun lelt : hrel X * hrel X => isEffectiveOrder (fst lelt) (snd lelt)).
Definition pairEffectiveOrder {X : UU} (le lt : hrel X) (is : isEffectiveOrder le lt) : EffectiveOrder X :=
  tpair _ (le,lt) is.

Definition EffectivelyOrderedSet :=
  total2 (fun X : hSet => EffectiveOrder X).
Definition pairEffectivelyOrderedSet {X : hSet} (is : EffectiveOrder X) : EffectivelyOrderedSet
  := tpair _ X is.
Definition pr1EffectivelyOrderedSet : EffectivelyOrderedSet -> hSet := pr1.

Definition EOle {X : EffectivelyOrderedSet} : po (pr1 X) :=
  let R := pr2 X in
  popair (fst (pr1 R)) (pr1 (pr1 (pr2 R))).
Definition EOge {X : EffectivelyOrderedSet} : po (pr1 X) :=
  po_reverse (@EOle X).

Definition EOlt {X : EffectivelyOrderedSet} : StrictPartialOrder (pr1 X) :=
  let R := pr2 X in
  pairStrictPartialOrder (snd (pr1 R)) (pr2 (pr1 (pr2 R))).
Definition EOgt {X : EffectivelyOrderedSet} : StrictPartialOrder (pr1 X) :=
  StrictPartialOrder_reverse (@EOlt X).

Definition PosetEffectiveOrder (X : EffectivelyOrderedSet) : Poset :=
  Posetpair _ (@EOle X).
Coercion PosetEffectiveOrder : EffectivelyOrderedSet >-> Poset.

Delimit Scope eo_scope with eo.

Notation "x <= y" := (EOle x y) : eo_scope.
Notation "x >= y" := (EOge x y) : eo_scope.
Notation "x < y" := (EOlt x y) : eo_scope.
Notation "x > y" := (EOgt x y) : eo_scope.

(** ** Complete Ordered Space *)

Open Scope eo_scope.

Section LeastUpperBound.

Context {X : Poset}.
Local Notation "x <= y" := (pr2 X x y).
  
Definition isUpperBound (E : subset X) (ub : X) : UU :=
  forall x : X, E x -> x <= ub.
Definition isSmallerThanUpperBounds (E : subset X) (lub : X) : UU :=
  forall ub : X, isUpperBound E ub -> lub <= ub.

Definition isLeastUpperBound (E : subset X) (lub : X) : UU :=
  dirprod (isUpperBound E lub) (isSmallerThanUpperBounds E lub).
Definition LeastUpperBound (E : subset X) : UU :=
  total2 (isLeastUpperBound E).
Definition pairLeastUpperBound (E : subset X) (lub : X)
           (is : isLeastUpperBound E lub) : LeastUpperBound E :=
  tpair (isLeastUpperBound E) lub is.
Definition pr1LeastUpperBound {E : subset X} :
  LeastUpperBound E -> X := pr1.

End LeastUpperBound.

Section GreatestLowerBound.

Context {X : Poset}.
Local Notation "x >= y" := (pr2 X y x).
  
Definition isLowerBound (E : subset X) (ub : X) : UU :=
  forall x : X, E x -> x >= ub.
Definition isBiggerThanLowerBounds (E : subset X) (lub : X) : UU :=
  forall ub : X, isLowerBound E ub -> lub >= ub.

Definition isGreatestLowerBound (E : subset X) (lub : X) : UU :=
  dirprod (isLowerBound E lub) (isBiggerThanLowerBounds E lub).
Definition GreatestLowerBound (E : subset X) : UU :=
  total2 (isGreatestLowerBound E).
Definition pairGreatestLowerBound (E : subset X) (lub : X)
           (is : isGreatestLowerBound E lub) : GreatestLowerBound E :=
  tpair (isGreatestLowerBound E) lub is.
Definition pr1GreatestLowerBound {E : subset X} :
  GreatestLowerBound E -> X := pr1.

End GreatestLowerBound.

Definition isCompleteSpace (X : Poset) :=
  forall E : subset X,
    hexists (isUpperBound E) -> hexists E -> LeastUpperBound E.
Definition CompleteSpace  :=
  total2 (fun X : Poset => isCompleteSpace X).
Definition pr1CompleteSpace : CompleteSpace -> UU := pr1.
Coercion pr1CompleteSpace : CompleteSpace >-> UU.

Close Scope eo_scope.