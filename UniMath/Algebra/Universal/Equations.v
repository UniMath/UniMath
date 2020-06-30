(** * Equations and varieties. *)

(**
   This file contains a formalization of equation systems and varieties of algebras.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.Universal.

Section Equations.

  Definition equation (sigma : signature) : UU
    := vterm sigma × vterm sigma.

  Definition lhs {sigma : signature} : equation sigma → vterm sigma := pr1.
  Definition rhs {sigma : signature} : equation sigma → vterm sigma := pr2.

  Definition holds {sigma : signature} (a:algebra sigma) (e:equation sigma) : UU
    := ∏ f, veval a f (lhs e) = veval a f (rhs e).

  Definition sysequations (sigma : signature) : UU
    := ∑ E : hSet, E → equation sigma.

  Definition eqidx {sigma : signature} : sysequations sigma → hSet := pr1.
  Coercion eqidx : sysequations >-> hSet.

  Definition geteq {sigma : signature} {sys : sysequations sigma}
    : sys → equation sigma
    := pr2 sys.

End Equations.

Section Varieties.

  Definition eqsignature : UU
    := ∑ sigma : signature, sysequations sigma.

  Definition signature_of_eqsignature : eqsignature → signature := pr1.
  Coercion signature_of_eqsignature : eqsignature >-> signature.

  Definition eqs (sigma : eqsignature) : sysequations sigma := pr2 sigma.

  Definition is_eqalgebra {sigma : eqsignature} (a : algebra sigma) : UU
    := ∏ e : eqs sigma, holds a (geteq e).

  Definition eqalgebra (sigma : eqsignature) : UU
    := ∑ a : algebra sigma, is_eqalgebra a.

  Definition algebra_of_eqalgebra {sigma : eqsignature}
    : eqalgebra sigma -> algebra sigma
    := pr1.
  Coercion algebra_of_eqalgebra : eqalgebra >-> algebra.

  Definition eqalgebra_is_eqalgebra {sigma : eqsignature} (a : eqalgebra sigma)
    : is_eqalgebra a
    := pr2 a.

End Varieties.
