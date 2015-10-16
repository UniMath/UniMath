(** * Division Rig *)
(** Definition of an algebraic structure (F,0,1,+,*,/) where:
- (F,0,+) is an abelian monoid
- (F\{0},1,*,/) is a group
- * distribute over + on both sides *)
(** Examples of such structure : non-negative rationnal numbers, non-negative real numbers *)

(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Import UniMath.Dedekind.Sets_comp.

(** ** More About Monoids *)

(** monoids *)

Definition ismonoid {X : hSet} (x0 : X) (op : binop X) : UU :=
  (isassoc op) × (isunit op x0).
Definition ismonoid_ismonoidop {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : ismonoidop op :=
  pr1 is,, x0,, pr2 is.

Definition ismonoid_isassoc {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isassoc op :=
  pr1 is.
Definition ismonoid_islunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : islunit op x0 :=
  pr1 (pr2 is).
Definition ismonoid_isrunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isrunit op x0 :=
  pr2 (pr2 is).

(** abelian monoids *)

Definition isabmonoid {X : hSet} (x0 : X) (op : binop X) : UU :=
  (ismonoid x0 op) × (iscomm op).
Definition isabmonoid_isabmonoidop {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isabmonoidop op :=
  ismonoid_ismonoidop (pr1 is),, pr2 is.

Definition isabmonoid_ismonoid {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : ismonoid x0 op :=
  pr1 is.
Definition isabmonoid_isassoc {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isassoc op :=
  ismonoid_isassoc (isabmonoid_ismonoid is).
Definition isabmonoid_islunit {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : islunit op x0 :=
  ismonoid_islunit (isabmonoid_ismonoid is).
Definition isabmonoid_isrunit {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isrunit op x0 :=
  ismonoid_isrunit (isabmonoid_ismonoid is).
Definition isabmonoid_iscomm {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : iscomm op :=
  pr2 is.

(** ** More About Groups *)

(** "additive" group *)

Definition isgr {X : hSet} (x0 : X) (op : binop X) (inv : unop X) : UU :=
  (ismonoid x0 op) × (isinv op x0 inv).
Definition isgr_isgrop {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : isgrop op :=
  ismonoid_ismonoidop (pr1 is),, inv,, pr2 is.
Coercion isgr_isgrop : isgr >-> isgrop.

Definition isgr_ismonoid {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : ismonoid x0 op :=
  pr1 is.
Definition isgr_isassoc {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : isassoc op :=
  ismonoid_isassoc (isgr_ismonoid is).
Definition isgr_islunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : islunit op x0 :=
  ismonoid_islunit (isgr_ismonoid is).
Definition isgr_isrunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : isrunit op x0 :=
  ismonoid_isrunit (isgr_ismonoid is).
Definition isgr_islinv {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : islinv op x0 inv :=
  pr1 (pr2 is).
Definition isgr_isrinv {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : isgr x0 op inv) : isrinv op x0 inv :=
  pr2 (pr2 is).

(** "multiplicative" group *)

Definition islinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtypes X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op (inv (x ,, Hx)) x = x1.
Definition isrinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtypes X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op x (inv (x ,, Hx)) = x1.
Definition isinv' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtypes X) (inv : subset exinv -> X)  :=
  islinv' x1 op exinv inv × isrinv' x1 op exinv inv.

Definition isgr' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtypes X) (inv : subset exinv -> X) : UU :=
  (ismonoid x1 op) × (isinv' x1 op exinv inv).

Definition isgr'_ismonoid {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : ismonoid x0 op :=
  pr1 is.
Definition isgr'_isassoc {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : isassoc op :=
  ismonoid_isassoc (isgr'_ismonoid is).
Definition isgr'_islunit {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : islunit op x0 :=
  ismonoid_islunit (isgr'_ismonoid is).
Definition isgr'_isrunit {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : isrunit op x0 :=
  ismonoid_isrunit (isgr'_ismonoid is).
Definition isgr'_islinv' {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : islinv' x0 op exinv inv :=
  pr1 (pr2 is).
Definition isgr'_isrinv' {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x0 op exinv inv) : isrinv' x0 op exinv inv :=
  pr2 (pr2 is).

Section isgr'_isgr.

Context {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}.
Context (is : isgr' x1 op exinv inv).
Context (Hx1 : exinv x1) (Hop : forall x y : X, exinv x -> exinv y -> exinv (op x y)) (Hinv : forall (x : X) (Hx : exinv x), exinv (inv (x ,, Hx))).

Definition x1' : subset exinv := x1 ,, Hx1.
Definition op' : binop (subset exinv) := fun x y => (op (pr1 x) (pr1 y)) ,, (Hop _ _ (pr2 x) (pr2 y)).
Definition inv' : unop (subset exinv) := λ y : subset exinv,
                                               match y with
                                               | x,, Hx => inv (x,, Hx),, Hinv x Hx
                                               end.
Lemma isassoc_op' : isassoc op'.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isassoc is).
Qed.
Lemma islunit_op'_x1' : islunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_islunit is).
Qed.
Lemma isrunit_op'_x1' : isrunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isrunit is).
Qed.
Lemma islinv_op'_x1'_inv' : islinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_islinv' is).
Qed.
Lemma isrinv_op'_x1'_inv' : isrinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isrinv' is).
Qed.

End isgr'_isgr.

Print isgr'_isgr.

Definition isgr'_isgr {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x1 op exinv inv)
           (Hx1 : exinv x1) (Hop : ∀ x y : X, exinv x -> exinv y -> exinv (op x y))
           (Hinv : ∀ (x : X) (Hx : exinv x), exinv (inv (x,, Hx))) : isgr (x1' Hx1) (op' Hop) (inv' Hinv) :=
  (isassoc_op' is Hop,, islunit_op'_x1' is Hx1 Hop,, isrunit_op'_x1' is Hx1 Hop)
    ,, (islinv_op'_x1'_inv' is Hx1 Hop Hinv,, isrinv_op'_x1'_inv' is Hx1 Hop Hinv).

(** ** More About Commutative Groups *)

(** "additive" group *)

Definition iscommgr {X : hSet} (x0 : X) (op : binop X) (inv : unop X) : UU :=
  (isgr x0 op inv) × (iscomm op).

Definition iscommgr_isgr {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : isgr x0 op inv :=
  pr1 is.
Definition iscommgr_isassoc {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : isassoc op :=
  isgr_isassoc (iscommgr_isgr is).
Definition iscommgr_islunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : islunit op x0 :=
  isgr_islunit (iscommgr_isgr is).
Definition iscommgr_isrunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : isrunit op x0 :=
  isgr_isrunit (iscommgr_isgr is).
Definition iscommgr_islinv {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : islinv op x0 inv :=
  isgr_islinv (iscommgr_isgr is).
Definition iscommgr_isrinv {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : isrinv op x0 inv :=
  isgr_isrinv(iscommgr_isgr is).
Definition iscommgr_iscomm {X : hSet} {x0 : X} {op : binop X} {inv : unop X} (is : iscommgr x0 op inv) : iscomm op :=
  pr2 is.

(** "multiplicative" group *)

Definition iscommgr' {X : hSet} (x1 : X) (op : binop X) (exinv : hsubtypes X) (inv : subset exinv -> X) : UU :=
  (isgr' x1 op exinv inv) × (iscomm op).

Definition iscommgr'_isgr' {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : isgr' x0 op exinv inv :=
  pr1 is.
Definition iscommgr'_isassoc {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : isassoc op :=
  isgr'_isassoc (iscommgr'_isgr' is).
Definition iscommgr'_islunit {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : islunit op x0 :=
  isgr'_islunit (iscommgr'_isgr' is).
Definition iscommgr'_isrunit {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : isrunit op x0 :=
  isgr'_isrunit (iscommgr'_isgr' is).
Definition iscommgr'_islinv' {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : islinv' x0 op exinv inv :=
  isgr'_islinv' (iscommgr'_isgr' is).
Definition iscommgr'_isrinv' {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : isrinv' x0 op exinv inv :=
  isgr'_isrinv' (iscommgr'_isgr' is).
Definition iscommgr'_iscomm {X : hSet} {x0 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x0 op exinv inv) : iscomm op :=
  pr2 is.

(*Section isgr'_isgr.

Context {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}.
Context (is : isgr' x1 op exinv inv).
Context (Hx1 : exinv x1) (Hop : forall x y : X, exinv x -> exinv y -> exinv (op x y)) (Hinv : forall (x : X) (Hx : exinv x), exinv (inv (x ,, Hx))).

Definition x1' : subset exinv := x1 ,, Hx1.
Definition op' : binop (subset exinv) := fun x y => (op (pr1 x) (pr1 y)) ,, (Hop _ _ (pr2 x) (pr2 y)).
Definition inv' : unop (subset exinv) := λ y : subset exinv,
                                               match y with
                                               | x,, Hx => inv (x,, Hx),, Hinv x Hx
                                               end.
Lemma isassoc_op' : isassoc op'.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isassoc is).
Qed.
Lemma islunit_op'_x1' : islunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_islunit is).
Qed.
Lemma isrunit_op'_x1' : isrunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isrunit is).
Qed.
Lemma islinv_op'_x1'_inv' : islinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_islinv' is).
Qed.
Lemma isrinv_op'_x1'_inv' : isrinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isrinv' is).
Qed.

End isgr'_isgr.

Definition isgr'_isgr {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : isgr' x1 op exinv inv)
           (Hx1 : exinv x1) (Hop : ∀ x y : X, exinv x -> exinv y -> exinv (op x y))
           (Hinv : ∀ (x : X) (Hx : exinv x), exinv (inv (x,, Hx))) : isgr (x1' Hx1) (op' Hop) (inv' Hinv) :=
  (isassoc_op' is Hop,, islunit_op'_x1' is Hx1 Hop,, isrunit_op'_x1' is Hx1 Hop)
    ,, (islinv_op'_x1'_inv' is Hx1 Hop Hinv,, isrinv_op'_x1'_inv' is Hx1 Hop Hinv).*)

(** ** Definition of a DivisionRig *)
(** to be a DivisionRig *)

Definition isDivisionRig {X : hSet} (x0 x1 : X) (plus mult : binop X) (Hnz : hsubtypes X) (inv : subset Hnz -> X) : UU :=
  dirprod (dirprod (isabmonoid x0 plus)
                   (iscommgr' x1 mult Hnz inv))
          (isdistr plus mult).

Definition isDivisionRig_isabmonoid {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isabmonoid x0 plus :=
  pr1 (pr1 is).
Definition isDivisionRig_isassoc_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isassoc plus :=
  isabmonoid_isassoc (isDivisionRig_isabmonoid is).
Definition isDivisionRig_islunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : islunit plus x0 :=
  isabmonoid_islunit (isDivisionRig_isabmonoid is).
Definition isDivisionRig_isrunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isrunit plus x0 :=
  isabmonoid_isrunit (isDivisionRig_isabmonoid is).
Definition isDivisionRig_iscomm_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : iscomm plus :=
  isabmonoid_iscomm (isDivisionRig_isabmonoid is).
Definition isDivisionRig_iscommgr' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : iscommgr' x1 mult Hnz inv :=
  pr2 (pr1 is).
Definition isDivisionRig_isassoc_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isassoc mult :=
  iscommgr'_isassoc (isDivisionRig_iscommgr' is).
Definition isDivisionRig_islunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : islunit mult x1 :=
  iscommgr'_islunit (isDivisionRig_iscommgr' is).
Definition isDivisionRig_isrunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isrunit mult x1 :=
  iscommgr'_isrunit (isDivisionRig_iscommgr' is).
Definition isDivisionRig_islinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : islinv' x1 mult Hnz inv :=
  iscommgr'_islinv' (isDivisionRig_iscommgr' is).
Definition isDivisionRig_isrinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isrinv' x1 mult Hnz inv :=
  iscommgr'_isrinv' (isDivisionRig_iscommgr' is).
Definition isDivisionRig_iscomm_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : iscomm mult :=
  iscommgr'_iscomm (isDivisionRig_iscommgr' is).
Definition isDivisionRig_isldistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isldistr plus mult :=
  pr1 (pr2 is).
Definition isDivisionRig_isrdistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivisionRig x0 x1 plus mult Hnz inv) : isrdistr plus mult :=
  pr2 (pr2 is).

(** DivisionRig *)

Definition DivisionRig : UU :=
  Σ (X : hSet), Σ (x0 x1 : X) (plus mult : binop X)  (Hnz : hsubtypes X) (inv : subset Hnz -> X),
    isDivisionRig x0 x1 plus mult Hnz inv.
Definition pr1DivisionRig (F : DivisionRig) : hSet := pr1 F.
Coercion pr1DivisionRig : DivisionRig >-> hSet.

Definition zeroDivisionRig {F : DivisionRig} : F := pr1 (pr2 F).
Definition oneDivisionRig {F : DivisionRig} : F := pr1 (pr2 (pr2 F)).
Definition plusDivisionRig {F : DivisionRig} : binop F := pr1 (pr2 (pr2 (pr2 F))).
Definition multDivisionRig {F : DivisionRig} : binop F := pr1 (pr2 (pr2 (pr2 (pr2 F)))).
Definition nzDivisionRig {F : DivisionRig} : hsubtypes (pr1 F) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Definition invDivisionRig {F : DivisionRig} : subset nzDivisionRig -> F := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F)))))).
Definition divDivisionRig {F : DivisionRig} : F -> subset nzDivisionRig -> F := fun x y => multDivisionRig x (invDivisionRig y).

Definition DivisionRig_isDivisionRig (F : DivisionRig) :
  isDivisionRig zeroDivisionRig oneDivisionRig plusDivisionRig multDivisionRig nzDivisionRig invDivisionRig :=
  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F))))))).

Definition isDivisionRig_DivisionRig {X : hSet}
           (x0 x1 : X) (plus mult : binop X) (Hnz : hsubtypes X) (inv : subset Hnz -> X)
  : isDivisionRig x0 x1 plus mult Hnz inv -> DivisionRig :=
  λ is : isDivisionRig x0 x1 plus mult Hnz inv, X ,, x0,, x1,, plus,, mult,, Hnz,, inv,, is.

Delimit Scope hf_scope with hf.

Notation "0" := zeroDivisionRig : hf_scope.
Notation "1" := oneDivisionRig : hf_scope.
Notation "x + y" := (plusDivisionRig x y) : hf_scope.
Notation "x * y" := (multDivisionRig x y) : hf_scope.
Notation "/ x" := (invDivisionRig x) : hf_scope.
Notation "x / y" := (divDivisionRig x y) : hf_scope.

Section DivisionRig_pty.

Open Scope hf_scope.
  
Context {F : DivisionRig}.

Definition DivisionRig_isassoc_plus:
  ∀ x y z : F, x + y + z = x + (y + z) :=
  isDivisionRig_isassoc_plus (DivisionRig_isDivisionRig F).
Definition DivisionRig_islunit_zero:
  ∀ x : F, 0 + x = x :=
  isDivisionRig_islunit_x0 (DivisionRig_isDivisionRig F).
Definition DivisionRig_isrunit_zero:
  ∀ x : F, x + 0 = x :=
  isDivisionRig_isrunit_x0 (DivisionRig_isDivisionRig F).
Definition DivisionRig_iscomm_plus:
  ∀ x y : F, x + y = y + x :=
  isDivisionRig_iscomm_plus (DivisionRig_isDivisionRig F).
Definition DivisionRig_isassoc_mult:
  ∀ x y z : F, x * y * z = x * (y * z) :=
  isDivisionRig_isassoc_mult (DivisionRig_isDivisionRig F).
Definition DivisionRig_islunit_one: 
  ∀ x : F, 1 * x = x :=
  isDivisionRig_islunit_x1 (DivisionRig_isDivisionRig F).
Definition DivisionRig_isrunit_one: 
  ∀ x : F, x * 1 = x :=
  isDivisionRig_isrunit_x1 (DivisionRig_isDivisionRig F).
Definition DivisionRig_islinv':
  ∀ (x : F) (Hx : nzDivisionRig x), / (x,, Hx) * x = 1 :=
  isDivisionRig_islinv' (DivisionRig_isDivisionRig F).
Definition DivisionRig_isrinv':
  ∀ (x : F) (Hx : nzDivisionRig x), x * / (x,, Hx) = 1 :=
  isDivisionRig_isrinv' (DivisionRig_isDivisionRig F).
Definition DivisionRig_iscomm_mult:
  ∀ x y : F, x * y = y * x :=
  isDivisionRig_iscomm_mult (DivisionRig_isDivisionRig F).
Definition DivisionRig_isldistr:
  ∀ x y z : F, z * (x + y) = z * x + z * y :=
  isDivisionRig_isldistr (DivisionRig_isDivisionRig F).
Definition DivisionRig_isrdistr: 
  ∀ x y z : F, (x + y) * z = x * z + y * z :=
  isDivisionRig_isrdistr (DivisionRig_isDivisionRig F).

Close Scope hf_scope.
                                                 
End DivisionRig_pty.



