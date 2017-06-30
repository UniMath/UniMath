(** Anthony Bordg, June 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Modules.

(** ********************************************

Contents:

- Bilinear morphisms between modules over a ring ([bilinearfun])
- algebras over a commutative ring ([algebra]) and associative, commutative, unital algebras ([assoc_comm_unital_algebra])
- Morphisms between (non-associative) algebras aver a commutative ring ([algebrafun])
- The opposite algebra ([algebra_opp])

***********************************************)


(** * Bilinear morphims between modules over a ring *)

Definition isbilinear {R : rng} (M N P : module R) (f : M -> N -> P) : UU :=
  (∏ x : M, islinear (λ y : N, f x y) ) × (∏ y : N, islinear (λ x : M, f x y)).

Definition bilinearfun {R : rng} (M N P : module R) : UU := ∑ f : M -> N -> P, isbilinear M N P f.

Definition pr1bilinearfun {R : rng} {M N P : module R} (f : bilinearfun M N P) : M -> N -> P := pr1 f.

Coercion pr1bilinearfun : bilinearfun >-> Funclass.


(** ** Algebras over a commutative ring *)

Section algebras.
Variable R : commrng.

(** Non-associative algebras over a commutative ring *)


Definition algebra : UU := ∑ M : module R, bilinearfun M M M.

Definition pr1algebra (A : algebra) : module R := pr1 A.

Coercion pr1algebra : algebra >-> module.

Definition algebra_pair (M : module R) (f : bilinearfun M M M) : algebra := tpair (λ X : module R, bilinearfun X X X) M f.

Definition mult_algebra (A : algebra) : binop A := pr1 (pr2 A).

Definition isbilinear_mult_algebra (A : algebra) : isbilinear A A A (mult_algebra A) := pr2 (pr2 A).

Notation "x * y" := (mult_algebra _ x y) : algebras_scope.

Delimit Scope algebras_scope with algebras.

(** Commutative algebras over a commutative ring *)

Definition iscomm_algebra (A : algebra) : UU := iscomm (mult_algebra A).

Definition commalgebra : UU := ∑ A : algebra, iscomm_algebra A.

Definition commalgebra_pair (A : algebra) (is : iscomm_algebra A) : commalgebra := tpair _ A is.

Definition commalgebra_to_algebra (A : commalgebra) : algebra := pr1 A.

Coercion commalgebra_to_algebra : commalgebra >-> algebra.

(** Associative  algebras over a commutative ring *)

Definition isassoc_algebra (A : algebra) : UU := isassoc (mult_algebra A).

Definition assocalgebra : UU := ∑ A : algebra, isassoc_algebra A.

Definition assocalgebra_pair (A : algebra) (is : isassoc_algebra A) : assocalgebra := tpair _ A is.

Definition assocalgebra_to_algebra (A : assocalgebra) : algebra := pr1 A.

Coercion assocalgebra_to_algebra : assocalgebra >-> algebra.

(** Unital algebras over a commutative ring *)

Definition isunital_algebra (A : algebra) : UU := isunital (mult_algebra A).

Definition unitalalgebra : UU := ∑ A : algebra, isunital_algebra A.

Definition unitalalgebra_pair (A : algebra) (is : isunital_algebra A) : unitalalgebra := tpair _ A is.

Definition unitalalgebra_to_algebra (A : unitalalgebra) : algebra := pr1 A.

Coercion unitalalgebra_to_algebra : unitalalgebra >-> algebra.

(** Associative, commutative, unital algebras over a ring *)

Definition assoc_comm_unital_algebra : UU := ∑ A : algebra, (isassoc_algebra A) × (iscomm_algebra A) × (isunital_algebra A).

(** Morphisms between (non-associative) algebras over a commutative ring *)

Local Open Scope algebras.

Definition algebrafun (A B : algebra) : UU := ∑ f : modulefun A B, ∏ x y : A, f (x * y) = f x * f y.

(** The opposite algebra  *)

Definition mult_opp (A : algebra) : A -> A -> A := λ x y: A, y * x.

Definition isbilinear_mult_opp (A : algebra) : isbilinear A A A (mult_opp A).
Proof.
  apply dirprodpair.
  - intro a. intros r b.
    apply (pr2  (isbilinear_mult_algebra A)).
  - intro b. intros r a.
    apply (pr1 (isbilinear_mult_algebra A)).
Defined.

Definition bilinear_mult_opp (A : algebra) : bilinearfun A A A := tpair _ (mult_opp A) (isbilinear_mult_opp A).

Definition algebra_opp (A : algebra) : algebra := tpair (λ X : module R, bilinearfun X X X) A (bilinear_mult_opp A).

End algebras.

(** To come : the definition of subalgebras and a proof that a subalgebra is an algebra *)