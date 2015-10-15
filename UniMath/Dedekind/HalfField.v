(** * Half Field *)
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

Definition ismonoid_isassoc {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isassoc op :=
  pr1 is.
Definition ismonoid_islunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : islunit op x0 :=
  pr1 (pr2 is).
Definition ismonoid_isrunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isrunit op x0 :=
  pr2 (pr2 is).

Definition ismonoid_ismonoidop {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : ismonoidop op :=
  pr1 is,, x0,, pr2 is.

(** abelian monoids *)

Definition isabmonoid {X : hSet} (x0 : X) (op : binop X) : UU :=
  (ismonoid x0 op) × (iscomm op).

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

Definition isabmonoid_isabmonoidop {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isabmonoidop op :=
  ismonoid_ismonoidop (pr1 is),, pr2 is.

(** ** More About Groups *)

Definition unop (X : UU) := X -> X.

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

Definition islinv' {X : hSet} (x1 : X) (op : binop X) (inv : unop X) (exinv : subsetcond X) :=
  forall x : X, exinv x -> op (inv x) x = x1.
Definition isrinv' {X : hSet} (x1 : X) (op : binop X) (inv : unop X) (exinv : subsetcond X) :=
  forall x : X, exinv x -> op x (inv x) = x1.
Definition isinv' {X : hSet} (x1 : X) (op : binop X) (inv : unop X) (exinv : subsetcond X) :=
  islinv' x1 op inv exinv × isrinv' x1 op inv exinv.

Definition isgr' {X : hSet} (x1 : X) (op : binop X) (inv : unop X) (exinv : subsetcond X) : UU :=
  (ismonoid x1 op) × (isinv' x1 op inv exinv).

Definition isgr'_ismonoid {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : ismonoid x0 op :=
  pr1 is.
Definition isgr'_isassoc {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : isassoc op :=
  ismonoid_isassoc (isgr'_ismonoid is).
Definition isgr'_islunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : islunit op x0 :=
  ismonoid_islunit (isgr'_ismonoid is).
Definition isgr'_isrunit {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : isrunit op x0 :=
  ismonoid_isrunit (isgr'_ismonoid is).
Definition isgr'_islinv' {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : islinv' x0 op inv exinv :=
  pr1 (pr2 is).
Definition isgr'_isrinv' {X : hSet} {x0 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X} (is : isgr' x0 op inv exinv) : isrinv' x0 op inv exinv :=
  pr2 (pr2 is).

Section isgr'_isgr.

Context {X : hSet} {x1 : X} {op : binop X} {inv : unop X} {exinv : subsetcond X}.
Context (is : isgr' x1 op inv exinv).
Context (Hx1 : exinv x1) (Hop : forall x y : X, exinv x -> exinv y -> exinv (op x y)) (Hinv : forall x : X, exinv x -> exinv (inv x)).

Definition x1' : subset exinv := x1 ,, Hx1.
Definition op' : binop (subset exinv) := fun x y => (op (pr1 x) (pr1 y)) ,, (Hop _ _ (pr2 x) (pr2 y)).
Definition inv' : unop (subset exinv) := fun x => (inv (pr1 x)) ,, (Hinv _ (pr2 x)).

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
  - apply (isgr'_islinv' is), Hx.
Qed.
Lemma isrinv_op'_x1'_inv' : isrinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgr'_isrinv' is), Hx.
Qed.

Definition isgr'_isgr : isgr x1' op' inv'.
Proof.
  repeat split.
  - exact isassoc_op'.
  - exact islunit_op'_x1'.
  - exact isrunit_op'_x1'.
  - exact islinv_op'_x1'_inv'.
  - exact isrinv_op'_x1'_inv'.
Defined.

End isgr'_isgr.

(** ** Definition *)

Definition isHalfField {X : hSet} (x0 x1 : X) (op1 op2 : binop X) (inv : unop X) (Hnz : subsetcond X) : UU :=
  dirprod (dirprod (isabmonoid x0 op1)
                   (isgr' x1 op2 inv Hnz))
          (isdistr op1 op2).

Definition isHalfField_isabmonoid {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : isabmonoid x0 op1 := pr1 (pr1 is).
Definition isHalfField_isassoc1 {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : isassoc op1 :=
  isabmonoid_isassoc (isHalfField_isabmonoid is).
Definition isHalfField_islunit1 {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : islunit op1 x0 :=
  isabmonoid_islunit (isHalfField_isabmonoid is).
Definition isHalfField_isrunit1 {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : isrunit op1 x0 :=
  isabmonoid_isrunit (isHalfField_isabmonoid is).
Definition isHalfField_iscomm1 {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : iscomm op1 :=
  isabmonoid_iscomm (isHalfField_isabmonoid is).
Definition isHalfField_isgr' {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : isgr' x1 op2 inv Hnz := pr2 (pr1 is).
Search isgr'.

Definition isHalfField_isdistr {X : hSet} {x0 x1 : X} {op1 op2 : binop X} {inv : unop X} {Hnz : subsetcond X} (is : isHalfField x0 x1 op1 op2 inv Hnz) : isdistr op1 op2 := pr2 is.