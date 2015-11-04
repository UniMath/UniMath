(** * Definition of appartness relationConstructive Algebraic Structures *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Foundations.Algebra.DivisionRig.
Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

Local Open Scope constructive_logic.

(** ** Constructive rig *)

Definition ConstructiveRig :=
  Σ X : apsetwith2binop, @isrigops X op1 op2.
Definition ConstructiveRig_set (X : ConstructiveRig) : apsetwith2binop := pr1 X.
Definition ConstructiveRig_rig : ConstructiveRig -> rig :=
  λ X : ConstructiveRig, (apsetwith2binop_setwith2binop (ConstructiveRig_set X)),, pr2 X.
Coercion ConstructiveRig_rig : ConstructiveRig >-> rig.

Definition CRigzero {X : ConstructiveRig} : X := rigunel1_is (pr2 X).
Definition CRigone {X : ConstructiveRig} : X := rigunel2_is (pr2 X).
Definition CRigplus {X : ConstructiveRig} : binop X := op1.
Definition CRigmult {X : ConstructiveRig} : binop X := op2.

Definition isnonzeroCR (X : ConstructiveRig) := @CRigone X # @CRigzero X.

(** ** Constructive commutative rig *)

Definition ConstructiveCommutativeRig :=
  Σ X : apsetwith2binop, @iscommrigops X op1 op2.
Definition ConstructiveCommutativeRig_CommutativeRig (X : ConstructiveCommutativeRig) : ConstructiveRig :=
  pr1 X,, pr1 (pr2 X).
Coercion ConstructiveCommutativeRig_CommutativeRig : ConstructiveCommutativeRig >-> ConstructiveRig.

(** ** Constructive ring *)

Definition ConstructiveRing := Σ X : apsetwith2binop, @isrngops X op1 op2.
Definition ConstructiveRing_set (X : ConstructiveRing) : apsetwith2binop := pr1 X.
Definition ConstructiveRing_rng : ConstructiveRing -> rng :=
  λ X : ConstructiveRing, (apsetwith2binop_setwith2binop (ConstructiveRing_set X)),, pr2 X.
Coercion ConstructiveRing_rng : ConstructiveRing >-> rng.

(** ** Constructive commutative ring *)

Definition ConstructiveCommutativeRing := Σ X : apsetwith2binop, @iscommrngops X op1 op2.
Definition ConstructiveCommutativeRing_CommutativeRing :
  ConstructiveCommutativeRing -> ConstructiveRing :=
  λ X : ConstructiveCommutativeRing, pr1 X,, pr1 (pr2 X).
Coercion ConstructiveCommutativeRing_CommutativeRing : ConstructiveCommutativeRing >-> ConstructiveRing.
Definition ConstructiveCommutativeRing_ConstructiveCommutativeRig :
  ConstructiveCommutativeRing -> ConstructiveCommutativeRig :=
  λ X : ConstructiveCommutativeRing, pr1 X,, (iscommrngopstoiscommrigops _ _ _ (pr2 X)).
Coercion ConstructiveCommutativeRing_ConstructiveCommutativeRig : ConstructiveCommutativeRing >-> ConstructiveCommutativeRig.

(** ** Constructive rig with division *)

Definition isConstrDivRig (X : ConstructiveRig) :=
  isnonzeroCR X × (∀ x : X, x # CRigzero -> multinvpair X x).

Definition ConstructiveDivisionRig := Σ X : ConstructiveRig, isConstrDivRig X.

(** ** Constructive commutative rig with division *)

Definition ConstructiveCommutativeDivisionRig := Σ X : ConstructiveCommutativeRig, isConstrDivRig X.

(** ** Constructive Field *)

Definition ConstructiveField := Σ X : ConstructiveCommutativeRing, isConstrDivRig X.
