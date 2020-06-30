(** * Equations and varieties. *)

(**
   This file contains a formalization of equation systems and varieties of algebras.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.Universal.

Section Equations.

  Definition equation (sigma : signature) (V: hSet) : UU
    := vterm sigma V × vterm sigma V.

  Definition sysequations (sigma : signature) (V: hSet) : UU
    := ∑ E : hSet, E → equation sigma V.

  Definition eqidx (sigma : signature) (V: hSet) : sysequations sigma V → hSet := pr1.
  Coercion eqidx : sysequations >-> hSet.

  Context {sigma: signature} {V: hSet}.

  Definition lhs : equation sigma V → vterm sigma V := pr1.
  Definition rhs : equation sigma V → vterm sigma V := pr2.

  Definition holds (a:algebra sigma) (e:equation sigma V) : UU
    := ∏ α, veval a α (lhs e) = veval a α (rhs e).

  Definition geteq {sys : sysequations sigma V}
    : sys → equation sigma V
    := pr2 sys.

End Equations.

Section Varieties.

  Definition eqsignature : UU
    := ∑ (sigma : signature) (V: hSet), sysequations sigma V.

  Definition signature_of_eqsignature : eqsignature → signature := pr1.
  Coercion signature_of_eqsignature : eqsignature >-> signature.

  Definition variables (sigma: eqsignature): hSet := pr1 (pr2 sigma).

  Definition eqs (sigma: eqsignature) : sysequations sigma (variables sigma) := pr2 (pr2 sigma).

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
