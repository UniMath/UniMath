(** * Varieties. *)

(**
This file contains a formalization of equational algebras, i.e., algebra which are
models of an equation system.
*)

Require Import UniMath.MoreFoundations.Notations.

Require Export UniMath.Algebra.Universal.Algebras.
Require Export UniMath.Algebra.Universal.Equations.

Section Varieties.

  Definition holds {σ: signature} {V: varspec σ} (a: algebra σ) (e: equation σ V) : UU
    := ∏ α, fromvterm a α (eqsort e) (lhs e) = fromvterm a α (eqsort e) (rhs e).

  Definition is_eqalgebra {σ : eqspec} (a : algebra σ) : UU
    := ∏ e: equations σ, holds a (geteq e).

  Definition eqalgebra (σ : eqspec) : UU
    := ∑ a : algebra σ, is_eqalgebra a.

  Definition algebra_of_eqalgebra {σ : eqspec}
    : eqalgebra σ -> algebra σ
    := pr1.
  Coercion algebra_of_eqalgebra : eqalgebra >-> algebra.

  Definition eqalgebra_proof {σ : eqspec} (a : eqalgebra σ)
    : is_eqalgebra a := pr2 a.

End Varieties.
