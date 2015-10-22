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

(** ** More about isunital *)

Definition unel_isunital {X : hSet} {op : binop X} (is : isunital op) : X := pr1 is.
Definition islunit_isunital {X : hSet} {op : binop X} (is : isunital op):
  (∀ x : X, op (unel_isunital is) x = x) :=
  pr1 (pr2 is).
Definition isrunit_isunital {X : hSet} {op : binop X} (is : isunital op):
  (∀ x : X, op x (unel_isunital is) = x) := pr2 (pr2 is).

(** ** More abour monoids *)

(** - assocax_is: ∀ (X : hSet) (opp : binop X), ismonoidop opp -> isassoc opp
  - unel_is: ∀ (X : hSet) (opp : binop X), ismonoidop opp -> X
  - lunax_is:
  ∀ (X : hSet) (opp : binop X) (is : ismonoidop opp),
  islunit opp (unel_is is)
  - runax_is:
  ∀ (X : hSet) (opp : binop X) (is : ismonoidop opp),
  isrunit opp (unel_is is) *)
           
Definition op_monoid (X : monoid) : binop X := op.
(** - assocax: ∀ X : monoid, isassoc op_monoid
  - unel: ∀ X : monoid, X
  - lunax: ∀ X : monoid, islunit op (unel X)
  - runax: ∀ X : monoid, isrunit op (unel X) *)

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

(** ** Definition of a DivRig *)
(** to be a DivRig *)

Require Import UniMath.Foundations.Algebra.Domains_and_Fields.

Definition isnonzerorig (X : rig) : UU := (1%rig : X) != 0%rig.

Definition isDivRig (X : commrig) : UU :=
  isnonzerorig X × (∀ x : X, x != 0%rig -> multinvpair X x).

Lemma isaprop_isDivRig (X : commrig) : isaprop (isDivRig X).
Proof.
  intro X.
  apply isofhleveldirprod.
  - now apply isapropneg.
  - apply impred_isaprop ; intro.
    apply isapropimpl.
    now apply isapropinvpair.
Qed.

Definition isDivRig_zero {X : commrig} (is : isDivRig X) : X := 0%rig.
Definition isDivRig_one {X : commrig} (is : isDivRig X) : X := 1%rig.
Definition isDivRig_plus {X : commrig} (is : isDivRig X) : binop X := λ x y : X, (x + y)%rig.
Definition isDivRig_mult {X : commrig} (is : isDivRig X) : binop X := λ x y : X, (x * y)%rig.
Definition isDivRig_inv {X : commrig} (is : isDivRig X) : subset (λ x : X, hProppair (x != isDivRig_zero is) (isapropneg _)) -> X :=
  λ x, pr1 ((pr2 is) (pr1 x) (pr2 x)).

Definition isDivRig_isassoc_plus {X : commrig} (is : isDivRig X) : isassoc (isDivRig_plus is)
  := rigassoc1 X.
Definition isDivRig_islunit_x0 {X : commrig} (is : isDivRig X) : islunit (isDivRig_plus is) (isDivRig_zero is)
  := riglunax1 X.
Definition isDivRig_isrunit_x0 {X : commrig} (is : isDivRig X) : isrunit (isDivRig_plus is) (isDivRig_zero is)
  := rigrunax1 X.
Definition isDivRig_iscomm_plus {X : commrig} (is : isDivRig X) : iscomm (isDivRig_plus is)
  := rigcomm1 X.

Definition isDivRig_isassoc_mult {X : commrig} (is : isDivRig X) : isassoc (isDivRig_mult is)
  := rigassoc2 X.
Definition isDivRig_islunit_x1 {X : commrig} (is : isDivRig X) : islunit (isDivRig_mult is) (isDivRig_one is)
  := riglunax2 X.
Definition isDivRig_isrunit_x1 {X : commrig} (is : isDivRig X) : isrunit (isDivRig_mult is) (isDivRig_one is)
  := rigrunax2 X.
Definition isDivRig_iscomm_mult {X : commrig} (is : isDivRig X) : iscomm (isDivRig_mult is)
  := rigcomm2 X.

Definition isDivRig_islinv {X : commrig} (is : isDivRig X) :
  ∀ (x : X) (Hx : x != isDivRig_zero is), isDivRig_mult is (isDivRig_inv is (x,, Hx)) x = isDivRig_one is
  := λ (x : X) (Hx : x != isDivRig_zero is), pr1 (pr2 (pr2 is x Hx)).
Definition isDivRig_isrinv {X : commrig} (is : isDivRig X) :
  ∀ (x : X) (Hx : x != isDivRig_zero is), isDivRig_mult is x (isDivRig_inv is (x,, Hx)) = isDivRig_one is
  := λ (x : X) (Hx : x != isDivRig_zero is), pr2 (pr2 (pr2 is x Hx)).

Definition isDivRig_isldistr {X : commrig} (is : isDivRig X) : isldistr (isDivRig_plus is) (isDivRig_mult is) := rigldistr X.
Definition isDivRig_isrdistr {X : commrig} (is : isDivRig X) : isrdistr (isDivRig_plus is) (isDivRig_mult is) := rigrdistr X.

(** DivRig *)

Definition DivRig : UU :=
  Σ (X : commrig), isDivRig X.
Definition pr1DivRig (F : DivRig) : hSet := pr1 F.
Coercion pr1DivRig : DivRig >-> hSet.

Definition zeroDivRig {F : DivRig} : F := isDivRig_zero (pr2 F).
Definition oneDivRig {F : DivRig} : F := isDivRig_one (pr2 F).
Definition plusDivRig {F : DivRig} : binop F := isDivRig_plus (pr2 F).
Definition multDivRig {F : DivRig} : binop F := isDivRig_mult (pr2 F).
Definition invDivRig {F : DivRig} : subset (λ x : F, hProppair (x != zeroDivRig) (isapropneg _)) -> F := isDivRig_inv (pr2 F).
Definition divDivRig {F : DivRig} : F -> subset (λ x : F, hProppair (x != zeroDivRig) (isapropneg _)) -> F := fun x y => multDivRig x (invDivRig y).

Definition DivRig_isDivRig (F : DivRig) :
  isDivRig (pr1 F) := (pr2 F).

Definition isDivRig_DivRig {X : commrig} : isDivRig X -> DivRig :=
λ is : isDivRig X, X ,, is.

Delimit Scope hf_scope with hf.

Notation "0" := zeroDivRig : hf_scope.
Notation "1" := oneDivRig : hf_scope.
Notation "x + y" := (plusDivRig x y) : hf_scope.
Notation "x * y" := (multDivRig x y) : hf_scope.
Notation "/ x" := (invDivRig x) : hf_scope.
Notation "x / y" := (divDivRig x y) : hf_scope.

Section DivRig_pty.

Open Scope hf_scope.
  
Context {F : DivRig}.

Definition DivRig_isassoc_plus:
  ∀ x y z : F, x + y + z = x + (y + z) :=
  isDivRig_isassoc_plus (DivRig_isDivRig F).
Definition DivRig_islunit_zero:
  ∀ x : F, 0 + x = x :=
  isDivRig_islunit_x0 (DivRig_isDivRig F).
Definition DivRig_isrunit_zero:
  ∀ x : F, x + 0 = x :=
  isDivRig_isrunit_x0 (DivRig_isDivRig F).
Definition DivRig_iscomm_plus:
  ∀ x y : F, x + y = y + x :=
  isDivRig_iscomm_plus (DivRig_isDivRig F).

Definition DivRig_isassoc_mult:
  ∀ x y z : F, x * y * z = x * (y * z) :=
  isDivRig_isassoc_mult (DivRig_isDivRig F).
Definition DivRig_islunit_one: 
  ∀ x : F, 1 * x = x :=
  isDivRig_islunit_x1 (DivRig_isDivRig F).
Definition DivRig_isrunit_one: 
  ∀ x : F, x * 1 = x :=
  isDivRig_isrunit_x1 (DivRig_isDivRig F).
Definition DivRig_iscomm_mult:
  ∀ x y : F, x * y = y * x :=
  isDivRig_iscomm_mult (DivRig_isDivRig F).

Definition DivRig_islinv:
  ∀ (x : F) (Hx : x != 0), / (x,, Hx) * x = 1 :=
  isDivRig_islinv (DivRig_isDivRig F).
Definition DivRig_isrinv:
  ∀ (x : F) (Hx : x != 0), x * / (x,, Hx) = 1 :=
  isDivRig_isrinv (DivRig_isDivRig F).

Definition DivRig_isldistr:
  ∀ x y z : F, z * (x + y) = z * x + z * y :=
  isDivRig_isldistr (DivRig_isDivRig F).
Definition DivRig_isrdistr: 
  ∀ x y z : F, (x + y) * z = x * z + y * z :=
  isDivRig_isrdistr (DivRig_isDivRig F).

Close Scope hf_scope.
                                                 
End DivRig_pty.
