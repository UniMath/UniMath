(** * Complements about groups *)

(** Catherine Lelay. Oct. 2015 - *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Ktheory.Group.
Require Export UniMath.Ktheory.AbelianGroup.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Monoid_comp.

(** ** More abour invstruct *)

Definition inv_invstruct {X : hSet} {opp : binop X} {is1 : ismonoidop opp} (is : invstruct opp is1) : unop X := pr1 is.
Definition islinv_invstruct {X : hSet} {opp : binop X} {is1 : ismonoidop opp} (is : invstruct opp is1) : islinv opp (unel_is is1) (inv_invstruct is) := pr1 (pr2 is).
Definition isrinv_invstruct {X : hSet} {opp : binop X} {is1 : ismonoidop opp} (is : invstruct opp is1) : isrinv opp (unel_is is1) (inv_invstruct is) := pr2 (pr2 is).

(** invstruct for partial inverse function *)

Definition islinv' {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op (inv (x ,, Hx)) x = x1.
Definition isrinv' {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X) :=
  forall (x : X) (Hx : exinv x), op x (inv (x ,, Hx)) = x1.
Definition isinv' {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X) :=
  islinv' op x1 exinv inv × isrinv' op x1 exinv inv.
Definition invstruct' {X : hSet} (op : binop X) (is : ismonoidop op) exinv :=
  Σ inv, isinv' op (unel_is is) exinv inv.

Lemma isaprop_islinv':
  forall {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X),
    isaprop (islinv' op x1 exinv inv).
Proof.
  intros.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro Hx.
  apply setproperty.
Qed.
Lemma isaprop_isrinv':
  forall {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X),
    isaprop (isrinv' op x1 exinv inv).
Proof.
  intros.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro Hx.
  apply setproperty.
Qed.
Lemma isaprop_isinv':
  forall {X : hSet} (op : binop X) (x1 : X) (exinv : hsubtypes X) (inv : subset exinv -> X),
    isaprop (isinv' op x1 exinv inv).
Proof.
  intros.
  apply isapropdirprod.
  now apply isaprop_islinv'.
  now apply isaprop_isrinv'.
Qed.
Lemma isaprop_invstruct' {X : hSet} (op : binop X) (is : ismonoidop op) exinv : isaprop (invstruct' op is exinv).
Proof.
  intros.
  apply (isapropsubtype (λ x : subset exinv -> X, hProppair _ (isaprop_isinv' _ _ _ _))).
  intros f g (Hfl,Hfr) (Hgl,Hgr).
  apply funextfun.
  intros (x,Hx).
  rewrite <- (lunax_is is (f (x,,Hx))).
  change (pr1 (pr2 is)) with (unel_is is).
  rewrite <- (Hgl x Hx).
  rewrite (assocax_is is).
  rewrite (Hfr x Hx).
  now apply runax_is.
Qed.

(** ** More About Groups *)

(** "multiplicative" group *)

Definition isgrop' {X : hSet} (op : binop X) exinv :=
  Σ is : ismonoidop op, invstruct' op is exinv.

Definition gr' := Σ X : setwithbinop, Σ exinv, @isgrop' X op exinv.

Definition isgrop'_ismonoidop {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : ismonoidop op :=
  pr1 is.
Definition isgrop'_isassoc {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : isassoc op :=
  assocax_is (isgrop'_ismonoidop is).
Definition isgrop'_unel {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : X := unel_is (isgrop'_ismonoidop is).
Definition isgrop'_islunit {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : islunit op (isgrop'_unel is) :=
  lunax_is (isgrop'_ismonoidop is).
Definition isgrop'_isrunit {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : isrunit op (isgrop'_unel is) :=
  runax_is (isgrop'_ismonoidop is).
Definition isgrop'_inv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : subset exinv -> X :=
  pr1 (pr2 is).
Definition isgrop'_islinv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : islinv' op (isgrop'_unel is) exinv (isgrop'_inv' is) :=
  pr1 (pr2 (pr2 is)).
Definition isgrop'_isrinv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' op exinv) : isrinv' op (isgrop'_unel is) exinv (isgrop'_inv' is) :=
  pr2 (pr2 (pr2 is)).

(* Section isgrop'_isgrop.

Context {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X}.
Context (is : isgrop' x1 op exinv).
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
  - apply (isgrop'_isassoc is).
Qed.
Lemma islunit_op'_x1' : islunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_islunit is).
Qed.
Lemma isrunit_op'_x1' : isrunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_isrunit is).
Qed.
Lemma islinv_op'_x1'_inv' : islinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_islinv' is).
Qed.
Lemma isrinv_op'_x1'_inv' : isrinv op' x1' inv'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_isrinv' is).
Qed.

End isgrop'_isgrop.

Definition isgrop'_isgrop {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' x1 op exinv)
           (Hx1 : exinv x1) (Hop : ∀ x y : X, exinv x -> exinv y -> exinv (op x y))
           (Hinv : ∀ (x : X) (Hx : exinv x), exinv (inv (x,, Hx))) : isgrop (x1' Hx1) (op' Hop) (inv' Hinv) :=
  (isassoc_op' is Hop,, islunit_op'_x1' is Hx1 Hop,, isrunit_op'_x1' is Hx1 Hop)
    ,, (islinv_op'_x1'_inv' is Hx1 Hop Hinv,, isrinv_op'_x1'_inv' is Hx1 Hop Hinv).*)

(** ** More About Commutative Groups *)

(** "multiplicative" group *)

Definition isabgrop' {X : hSet} (op : binop X) exinv : UU :=
  (isgrop' op exinv) × (iscomm op).

Definition abgr' := Σ X : setwithbinop, Σ exinv, @isabgrop' X op exinv.

Definition isabgrop'_isgrop' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : isgrop' op exinv :=
  pr1 is.
Definition isabgrop'_isassoc {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : isassoc op :=
  isgrop'_isassoc (isabgrop'_isgrop' is).
Definition isabgrop'_unel {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : X :=
  isgrop'_unel (isabgrop'_isgrop' is).
Definition isabgrop'_islunit {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : islunit op (isabgrop'_unel is) :=
  isgrop'_islunit (isabgrop'_isgrop' is).
Definition isabgrop'_isrunit {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : isrunit op (isabgrop'_unel is) :=
  isgrop'_isrunit (isabgrop'_isgrop' is).
Definition isabgrop'_inv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : subset exinv -> X :=
  isgrop'_inv' (isabgrop'_isgrop' is).
Definition isabgrop'_islinv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : islinv' op (isabgrop'_unel is) exinv (isabgrop'_inv' is) :=
  isgrop'_islinv' (isabgrop'_isgrop' is).
Definition isabgrop'_isrinv' {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : isrinv' op (isabgrop'_unel is) exinv (isabgrop'_inv' is) :=
  isgrop'_isrinv' (isabgrop'_isgrop' is).
Definition isabgrop'_iscomm {X : hSet} {op : binop X} {exinv : hsubtypes X}
           (is : isabgrop' op exinv) : iscomm op :=
  pr2 is.

(*Section isgrop'_isgr.

Context {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X}.
Context (is : isgrop' x1 op exinv).
Context (Hx1 : exinv x1) (Hop : forall x y : X, exinv x -> exinv y -> exinv (op x y)) (Hinv : forall (x : X) (Hx : exinv x), exinv (inv (x ,, Hx))).

Definition x1' : subset exinv := x1 ,, Hx1.
Definition op' : binop (subset exinv) := fun x y => (op (pr1 x) (pr1 y)) ,, (Hop _ _ (pr2 x) (pr2 y)).
Definition' : unop (subset exinv) := λ y : subset exinv,
                                               match y with
                                               | x,, Hx => (x,, Hx),, Hinv x Hx
                                               end.
Lemma isassoc_op' : isassoc op'.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_isassoc is).
Qed.
Lemma islunit_op'_x1' : islunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_islunit is).
Qed.
Lemma isrunit_op'_x1' : isrunit op' x1'.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_isrunit is).
Qed.
Lemma islinv_op'_x1'_inv' : islinv op' x1''.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_islinv' is).
Qed.
Lemma isrinv_op'_x1'_inv' : isrinv op' x1''.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl.
  - apply pr2.
  - apply (isgrop'_isrinv' is).
Qed.

End isgrop'_isgr.

Definition isgrop'_isgr {X : hSet} {x1 : X} {op : binop X} {exinv : hsubtypes X}
           (is : isgrop' x1 op exinv)
           (Hx1 : exinv x1) (Hop : ∀ x y : X, exinv x -> exinv y -> exinv (op x y))
           (Hinv : ∀ (x : X) (Hx : exinv x), exinv (inv (x,, Hx))) : isgr (x1' Hx1) (op' Hop) (inv' Hinv) :=
  (isassoc_op' is Hop,, islunit_op'_x1' is Hx1 Hop,, isrunit_op'_x1' is Hx1 Hop)
    ,, (islinv_op'_x1'_inv' is Hx1 Hop Hinv,, isrinv_op'_x1'_inv' is Hx1 Hop Hinv).*)

