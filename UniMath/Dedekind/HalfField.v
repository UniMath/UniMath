(** * Half Field *)
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


(** ** Definition of a HalField *)
(** to be a HalfField *)

Definition isHalfField {X : hSet} (x0 x1 : X) (plus mult : binop X) (Hnz : subsetcond X) (inv : subset Hnz -> X) : UU :=
  dirprod (dirprod (isabmonoid x0 plus)
                   (iscommgr' x1 mult Hnz inv))
          (isdistr plus mult).

Definition isHalfField_isabmonoid {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isabmonoid x0 plus :=
  pr1 (pr1 is).
Definition isHalfField_isassoc_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isassoc plus :=
  isabmonoid_isassoc (isHalfField_isabmonoid is).
Definition isHalfField_islunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : islunit plus x0 :=
  isabmonoid_islunit (isHalfField_isabmonoid is).
Definition isHalfField_isrunit_x0 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isrunit plus x0 :=
  isabmonoid_isrunit (isHalfField_isabmonoid is).
Definition isHalfField_iscomm_plus {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : iscomm plus :=
  isabmonoid_iscomm (isHalfField_isabmonoid is).
Definition isHalfField_iscommgr' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : iscommgr' x1 mult Hnz inv :=
  pr2 (pr1 is).
Definition isHalfField_isassoc_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isassoc mult :=
  iscommgr'_isassoc (isHalfField_iscommgr' is).
Definition isHalfField_islunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : islunit mult x1 :=
  iscommgr'_islunit (isHalfField_iscommgr' is).
Definition isHalfField_isrunit_x1 {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isrunit mult x1 :=
  iscommgr'_isrunit (isHalfField_iscommgr' is).
Definition isHalfField_islinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : islinv' x1 mult Hnz inv :=
  iscommgr'_islinv' (isHalfField_iscommgr' is).
Definition isHalfField_isrinv' {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isrinv' x1 mult Hnz inv :=
  iscommgr'_isrinv' (isHalfField_iscommgr' is).
Definition isHalfField_iscomm_mult {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : iscomm mult :=
  iscommgr'_iscomm (isHalfField_iscommgr' is).
Definition isHalfField_isldistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isldistr plus mult :=
  pr1 (pr2 is).
Definition isHalfField_isrdistr {X : hSet} {x0 x1 : X} {plus mult : binop X} {Hnz : subsetcond X} {inv : subset Hnz -> X}
           (is : isHalfField x0 x1 plus mult Hnz inv) : isrdistr plus mult :=
  pr2 (pr2 is).

(** HalfField *)

Definition HalfField : UU :=
  Σ (X : hSet), Σ (x0 x1 : X) (plus mult : binop X)  (Hnz : subsetcond X) (inv : subset Hnz -> X),
    isHalfField x0 x1 plus mult Hnz inv.
Definition pr1HalfField (F : HalfField) : hSet := pr1 F.
Coercion pr1HalfField : HalfField >-> hSet.

Definition zeroHalfField {F : HalfField} : F := pr1 (pr2 F).
Definition oneHalfField {F : HalfField} : F := pr1 (pr2 (pr2 F)).
Definition plusHalfField {F : HalfField} : binop F := pr1 (pr2 (pr2 (pr2 F))).
Definition multHalfField {F : HalfField} : binop F := pr1 (pr2 (pr2 (pr2 (pr2 F)))).
Definition nzHalfField {F : HalfField} : subsetcond (pr1 F) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Definition invHalfField {F : HalfField} : subset nzHalfField -> F := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F)))))).
Definition divHalfField {F : HalfField} : F -> subset nzHalfField -> F := fun x y => multHalfField x (invHalfField y).

Definition HalfField_isHalfField (F : HalfField) :
  isHalfField zeroHalfField oneHalfField plusHalfField multHalfField nzHalfField invHalfField :=
  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 F))))))).

Definition isHalfField_HalfField {X : hSet}
           (x0 x1 : X) (plus mult : binop X) (Hnz : subsetcond X) (inv : subset Hnz -> X)
  : isHalfField x0 x1 plus mult Hnz inv -> HalfField :=
  λ is : isHalfField x0 x1 plus mult Hnz inv, X ,, x0,, x1,, plus,, mult,, Hnz,, inv,, is.

Delimit Scope hf_scope with hf.

Notation "0" := zeroHalfField : hf_scope.
Notation "1" := oneHalfField : hf_scope.
Notation "x + y" := (plusHalfField x y) : hf_scope.
Notation "x * y" := (multHalfField x y) : hf_scope.
Notation "/ x" := (invHalfField x) : hf_scope.
Notation "x / y" := (divHalfField x y) : hf_scope.

Section HalfField_pty.

Open Scope hf_scope.
  
Context {F : HalfField}.

Definition HalfField_isassoc_plus:
  ∀ x y z : F, x + y + z = x + (y + z) :=
  isHalfField_isassoc_plus (HalfField_isHalfField F).
Definition HalfField_islunit_zero:
  ∀ x : F, 0 + x = x :=
  isHalfField_islunit_x0 (HalfField_isHalfField F).
Definition HalfField_isrunit_zero:
  ∀ x : F, x + 0 = x :=
  isHalfField_isrunit_x0 (HalfField_isHalfField F).
Definition HalfField_iscomm_plus:
  ∀ x y : F, x + y = y + x :=
  isHalfField_iscomm_plus (HalfField_isHalfField F).
Definition HalfField_isassoc_mult:
  ∀ x y z : F, x * y * z = x * (y * z) :=
  isHalfField_isassoc_mult (HalfField_isHalfField F).
Definition HalfField_islunit_one: 
  ∀ x : F, 1 * x = x :=
  isHalfField_islunit_x1 (HalfField_isHalfField F).
Definition HalfField_isrunit_one: 
  ∀ x : F, x * 1 = x :=
  isHalfField_isrunit_x1 (HalfField_isHalfField F).
Definition HalfField_islinv':
  ∀ (x : F) (Hx : nzHalfField x), / (x,, Hx) * x = 1 :=
  isHalfField_islinv' (HalfField_isHalfField F).
Definition HalfField_isrinv':
  ∀ (x : F) (Hx : nzHalfField x), x * / (x,, Hx) = 1 :=
  isHalfField_isrinv' (HalfField_isHalfField F).
Definition HalfField_iscomm_mult:
  ∀ x y : F, x * y = y * x :=
  isHalfField_iscomm_mult (HalfField_isHalfField F).
Definition HalfField_isldistr:
  ∀ x y z : F, z * (x + y) = z * x + z * y :=
  isHalfField_isldistr (HalfField_isHalfField F).
Definition HalfField_isrdistr: 
  ∀ x y z : F, (x + y) * z = x * z + y * z :=
  isHalfField_isrdistr (HalfField_isHalfField F).

Close Scope hf_scope.
                                                 
End HalfField_pty.

(** ** Subset of a half field *)

