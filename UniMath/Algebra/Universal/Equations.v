(** * Equations and varieties. *)

(**
   This file contains a formalization of equation systems and varieties of algebras.
 *)

Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.FreeAlgebras.

Section Equations.

  Definition equation_bare (σ : signature) (V: varspec σ): sUU (sorts σ)
    := λ s: sorts σ, vterm σ V s × vterm σ V s.

  Definition lhs {σ : signature} {V: varspec σ} {s: sorts σ}
    : equation_bare σ V s → vterm σ V s := pr1.

  Definition rhs {σ : signature} {V: varspec σ} {s: sorts σ}
    : equation_bare σ V s → vterm σ V s := pr2.

  Definition equation (σ : signature) (V: varspec σ): UU
    := ∑ s: sorts σ, equation_bare σ V s.
 
  Definition eqsort {σ: signature} {V: varspec σ} (e: equation σ V)
    : sorts σ := pr1 e.

  Coercion eqbare {σ: signature} {V: varspec σ} (e: equation σ V)
    : equation_bare σ V (eqsort e) := pr2 e.

  Definition sysequations (σ : signature) (V: varspec σ): UU
    := ∑ E : hSet, E → equation σ V.

  Definition syseqidx (σ : signature) (V: varspec σ): sysequations σ V → hSet := pr1.
  Coercion syseqidx : sysequations >-> hSet.

  Definition geteq {σ: signature} {V: varspec σ} {sys : sysequations σ V}: sys → equation σ V
    := pr2 sys.

  Definition holds {σ: signature} {V: varspec σ} (a: algebra σ) (e: equation σ V) : UU
    := ∏ α, veval a α (eqsort e) (lhs e) = veval a α (eqsort e) (rhs e).

End Equations.

Section Varieties.

  Definition eqsignature: UU 
    := ∑ (σ : signature) (V: varspec σ), sysequations σ V.

  Definition eqsign_signature: eqsignature → signature := pr1.
  Coercion eqsign_signature : eqsignature >-> signature.

  Definition eqsign_variables (σ: eqsignature): varspec σ := pr1 (pr2 σ).

  Definition eqs (σ: eqsignature): sysequations σ (eqsign_variables σ) := pr2 (pr2 σ).

  Definition is_eqalgebra {σ : eqsignature} (a : algebra σ) : UU
    := ∏ e: eqs σ, holds a (geteq e).

  Definition eqalgebra (σ : eqsignature) : UU
    := ∑ a : algebra σ, is_eqalgebra a.

  Definition algebra_of_eqalgebra {σ : eqsignature}
    : eqalgebra σ -> algebra σ
    := pr1.
  Coercion algebra_of_eqalgebra : eqalgebra >-> algebra.

  Definition eqalgebra_is_eqalgebra {σ : eqsignature} (a : eqalgebra σ)
    : is_eqalgebra a
    := pr2 a.

End Varieties.
