(** * Division Rig *)
(** Definition of an algebraic structure (F,0,1,+,*,/) where:
- (F,0,+) is an abelian monoid
- (F\{0},1,*,/) is a group
- * distribute over + on both sides *)
(** Examples of such structure : non-negative rationnal numbers, non-negative real numbers *)

(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Monoid_comp.
Require Import UniMath.Dedekind.Group_comp.

(** ** Definition of a DivRig *)
(** to be a DivRig *)

Definition isDivRig {X : hSet} (plus mult : binop X) exinv : UU :=
  dirprod (dirprod (isabmonoidop plus)
                   (isabgrop' mult exinv))
          (isdistr plus mult).

Definition isDivRig_isabmonoid {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isabmonoidop plus :=
  pr1 (pr1 is).
Definition isDivRig_isassoc_plus {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isassoc plus :=
  pr1 (pr1 (isDivRig_isabmonoid is)).
Definition isDivRig_unel_plus {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : X :=
  unel_is (isDivRig_isabmonoid is).
Definition isDivRig_islunit_x0 {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : islunit plus (isDivRig_unel_plus is) :=
  lunax_is (isDivRig_isabmonoid is).
Definition isDivRig_isrunit_x0 {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isrunit plus (isDivRig_unel_plus is) :=
  runax_is (isDivRig_isabmonoid is).
Definition isDivRig_iscomm_plus {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : iscomm plus :=
  commax_is (isDivRig_isabmonoid is).
Definition isDivRig_isabgrop' {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isabgrop' mult exinv :=
  pr2 (pr1 is).
Definition isDivRig_isassoc_mult {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isassoc mult :=
  isabgrop'_isassoc (isDivRig_isabgrop' is).
Definition isDivRig_unel_mult {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : X :=
  isabgrop'_unel (isDivRig_isabgrop' is).
Definition isDivRig_islunit_x1 {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : islunit mult (isDivRig_unel_mult is) :=
  isabgrop'_islunit (isDivRig_isabgrop' is).
Definition isDivRig_isrunit_x1 {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isrunit mult (isDivRig_unel_mult is) :=
  isabgrop'_isrunit (isDivRig_isabgrop' is).
Definition isDivRig_inv' {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : subset exinv -> X :=
  isabgrop'_inv' (isDivRig_isabgrop' is).
Definition isDivRig_islinv' {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : islinv' mult (isDivRig_unel_mult is) exinv (isDivRig_inv' is) :=
  isabgrop'_islinv' (isDivRig_isabgrop' is).
Definition isDivRig_isrinv' {X : hSet}  {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isrinv' mult (isDivRig_unel_mult is) exinv (isDivRig_inv' is) :=
  isabgrop'_isrinv' (isDivRig_isabgrop' is).
Definition isDivRig_iscomm_mult {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : iscomm mult :=
  isabgrop'_iscomm (isDivRig_isabgrop' is).
Definition isDivRig_isldistr {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isldistr plus mult :=
  pr1 (pr2 is).
Definition isDivRig_isrdistr {X : hSet} {plus mult : binop X} {exinv}
           (is : isDivRig plus mult exinv) : isrdistr plus mult :=
  pr2 (pr2 is).

(** DivRig *)

Definition DivRig : UU :=
  Σ (X : setwith2binop), Σ exinv, @isDivRig X op1 op2 exinv.
Definition pr1DivRig (F : DivRig) : hSet := pr1 F.
Coercion pr1DivRig : DivRig >-> hSet.

Definition zeroDivRig {F : DivRig} : F := isDivRig_unel_plus (pr2 (pr2 F)).
Definition oneDivRig {F : DivRig} : F := isDivRig_unel_mult (pr2 (pr2 F)).
Definition plusDivRig {F : DivRig} : binop F := pr1 (pr2 (pr1 F)).
Definition multDivRig {F : DivRig} : binop F := pr2 (pr2 (pr1 F)).
Definition nzDivRig {F : DivRig} : hsubtypes (pr1 F) := pr1 (pr2 F).
Definition invDivRig {F : DivRig} : subset nzDivRig -> F := isDivRig_inv' (pr2 (pr2 F)).
Definition divDivRig {F : DivRig} : F -> subset nzDivRig -> F := fun x y => multDivRig x (invDivRig y).

Definition DivRig_isDivRig (F : DivRig) :
  isDivRig plusDivRig multDivRig nzDivRig :=
  pr2 (pr2 F).

Definition isDivRig_DivRig {X : hSet} (plus mult : binop X) exinv: isDivRig plus mult exinv -> DivRig :=
λ is : isDivRig plus mult exinv, (X,, plus,, mult),, exinv,, is.

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
Definition DivRig_islinv':
  ∀ (x : F) (Hx : nzDivRig x), / (x,, Hx) * x = 1 :=
  isDivRig_islinv' (DivRig_isDivRig F).
Definition DivRig_isrinv':
  ∀ (x : F) (Hx : nzDivRig x), x * / (x,, Hx) = 1 :=
  isDivRig_isrinv' (DivRig_isDivRig F).
Definition DivRig_iscomm_mult:
  ∀ x y : F, x * y = y * x :=
  isDivRig_iscomm_mult (DivRig_isDivRig F).
Definition DivRig_isldistr:
  ∀ x y z : F, z * (x + y) = z * x + z * y :=
  isDivRig_isldistr (DivRig_isDivRig F).
Definition DivRig_isrdistr: 
  ∀ x y z : F, (x + y) * z = x * z + y * z :=
  isDivRig_isrdistr (DivRig_isDivRig F).

Close Scope hf_scope.
                                                 
End DivRig_pty.
