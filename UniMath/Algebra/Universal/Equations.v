(** * Equations over a signature and equational theories *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
This file contains a formalization of equations and equation systems over a signature.
*)

Require Import UniMath.MoreFoundations.Notations.

Require Export UniMath.Algebra.Universal.VTerms.

Section Equations.

  (** An equation is a pair of terms (with variables) of the same sort *)

  Definition equation (σ : signature) (V: varspec σ): UU
    := ∑ s: sorts σ, term σ V s × term σ V s.

  Definition eqsort {σ: signature} {V: varspec σ} (eq: equation σ V)
    : sorts σ := pr1 eq.

  Definition lhs {σ : signature} {V: varspec σ} (eq: equation σ V): term σ V (eqsort eq) := pr12 eq.

  Definition rhs {σ : signature} {V: varspec σ} (eq: equation σ V): term σ V (eqsort eq) := pr22 eq.

  (**
  Since we do not have power types, we define an equation system as a type of equation
  identifiers endowed with a map from identifiers to equations.
  *)

  Definition eqsystem (σ : signature) (V: varspec σ): UU
    := ∑ E : UU, E → equation σ V.

  Definition eqsystemids (σ : signature) (V: varspec σ): eqsystem σ V → UU := pr1.

  Coercion eqsystemids : eqsystem >-> UU.

  Definition geteq {σ: signature} {V: varspec σ} {sys : eqsystem σ V}: sys → equation σ V
    := pr2 sys.

  (**
  An equational specification is a signature endowed with an equation system (and the
  necessary variable specification).
  *)

  Definition eqspec: UU  := ∑ (σ : signature) (V: varspec σ), eqsystem σ V.

  Definition signature_of_eqspec: eqspec → signature := pr1.

  Coercion signature_of_eqspec : eqspec >-> signature.

  Definition variables (σ: eqspec): varspec σ := pr12 σ.

  Definition equations (σ: eqspec): eqsystem σ (variables σ) := pr22 σ.

End Equations.
