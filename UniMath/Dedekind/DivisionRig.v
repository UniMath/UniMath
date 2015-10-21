(** * Division Rig *)
(** Definition of an algebraic structure (F,0,1,+,*,/) where:
- (F,0,+,* ) is a commutative
- / is a multiplicative inverse
- * distribute over + on both sides *)
(** Examples of such structure : non-negative rationnal numbers, non-negative real numbers *)

(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Foundations.Algebra.Domains_and_Fields.

(** ** Definition of a DivRig *)
(** to be a DivRig *)


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
