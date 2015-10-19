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

Definition isDivRig {X : hSet} (x0 x1 : X) (plus mult : binop X) (Hnz : hsubtypes X) (inv : subset Hnz -> X) : UU :=
  dirprod (dirprod (isabmonoid x0 plus)
                   (iscommgr' x1 mult Hnz inv))
          (isdistr plus mult).

Definition isDivRig_isabmonoid {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isabmonoid x0 plus :=
  pr1 (pr1 is).
Definition isDivRig_isassoc_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isassoc plus :=
  isabmonoid_isassoc (isDivRig_isabmonoid is).
Definition isDivRig_islunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : islunit plus x0 :=
  isabmonoid_islunit (isDivRig_isabmonoid is).
Definition isDivRig_isrunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isrunit plus x0 :=
  isabmonoid_isrunit (isDivRig_isabmonoid is).
Definition isDivRig_iscomm_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : iscomm plus :=
  isabmonoid_iscomm (isDivRig_isabmonoid is).
Definition isDivRig_iscommgr' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : iscommgr' x1 mult Hnz inv :=
  pr2 (pr1 is).
Definition isDivRig_isassoc_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isassoc mult :=
  iscommgr'_isassoc (isDivRig_iscommgr' is).
Definition isDivRig_islunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : islunit mult x1 :=
  iscommgr'_islunit (isDivRig_iscommgr' is).
Definition isDivRig_isrunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isrunit mult x1 :=
  iscommgr'_isrunit (isDivRig_iscommgr' is).
Definition isDivRig_islinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : islinv' x1 mult Hnz inv :=
  iscommgr'_islinv' (isDivRig_iscommgr' is).
Definition isDivRig_isrinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isrinv' x1 mult Hnz inv :=
  iscommgr'_isrinv' (isDivRig_iscommgr' is).
Definition isDivRig_iscomm_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : iscomm mult :=
  iscommgr'_iscomm (isDivRig_iscommgr' is).
Definition isDivRig_isldistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isldistr plus mult :=
  pr1 (pr2 is).
Definition isDivRig_isrdistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : hsubtypes X} {inv : subset Hnz -> X}
           (is : isDivRig x0 x1 plus mult Hnz inv) : isrdistr plus mult :=
  pr2 (pr2 is).

(** DivRig *)

Definition DivRig : UU :=
  Σ (X : hSet), Σ (x0 x1 : X) (plus mult : binop X)  (Hnz : hsubtypes X) (inv : subset Hnz -> X),
    isDivRig x0 x1 plus mult Hnz inv.
Definition pr1DivRig (F : DivRig) : hSet := pr1 F.
Coercion pr1DivRig : DivRig >-> hSet.

Definition zeroDivRig {F : DivRig} : F := pr1 (pr2 F).
Definition oneDivRig {F : DivRig} : F := pr1 (pr2 (pr2 F)).
Definition plusDivRig {F : DivRig} : binop F := pr1 (pr2 (pr2 (pr2 F))).
Definition multDivRig {F : DivRig} : binop F := pr1 (pr2 (pr2 (pr2 (pr2 F)))).
Definition nzDivRig {F : DivRig} : hsubtypes (pr1 F) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Definition invDivRig {F : DivRig} : subset nzDivRig -> F := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F)))))).
Definition divDivRig {F : DivRig} : F -> subset nzDivRig -> F := fun x y => multDivRig x (invDivRig y).

Definition DivRig_isDivRig (F : DivRig) :
  isDivRig zeroDivRig oneDivRig plusDivRig multDivRig nzDivRig invDivRig :=
  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F))))))).

Definition isDivRig_DivRig {X : hSet}
           (x0 x1 : X) (plus mult : binop X) (Hnz : hsubtypes X) (inv : subset Hnz -> X)
  : isDivRig x0 x1 plus mult Hnz inv -> DivRig :=
  λ is : isDivRig x0 x1 plus mult Hnz inv, X ,, x0,, x1,, plus,, mult,, Hnz,, inv,, is.

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



