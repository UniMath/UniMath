(** * Complements about groups *)

(** Catherine Lelay. Oct. 2015 - *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Ktheory.Group.
Require Export UniMath.Ktheory.AbelianGroup.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Monoid_comp.

(** ** More About Groups *)

(** *** "additive" group *)

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

(** *** "multiplicative" group *)
(** group defined on a subset *)

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

(** ** Commutative Groups *)

(** *** "additive" group *)

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

(** *** "multiplicative" group *)

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

Section iscommgr'_iscommgr.

Context {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}.
Context (is : iscommgr' x1 op exinv inv).
Context (Hx1 : exinv x1) (Hop : forall x y : X, exinv x -> exinv y -> exinv (op x y)) (Hinv : forall (x : X) (Hx : exinv x), exinv (inv (x ,, Hx))).

Lemma iscomm_op' : iscomm (op' Hop).
Proof.
  intros (x,Hx) (y,Hy).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply (iscommgr'_iscomm is).
Qed.
                                  
End iscommgr'_iscommgr.

Definition iscommgr'_iscommgr {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X} {inv : subset exinv -> X}
           (is : iscommgr' x1 op exinv inv)
           (Hx1 : exinv x1) (Hop : ∀ x y : X, exinv x -> exinv y -> exinv (op x y))
           (Hinv : ∀ (x : X) (Hx : exinv x), exinv (inv (x,, Hx))) : iscommgr (x1' Hx1) (op' Hop) (inv' Hinv) :=
  isgr'_isgr (iscommgr'_isgr' is) Hx1 Hop Hinv,, iscomm_op' is Hop.
