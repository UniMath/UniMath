(** ** A final coalgebra of a polynomial functor defined by sets is a set.

    Author : Antoine Fisse (@AextraT), 2025
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.MWithSets.
Require Import UniMath.Induction.M.Uniqueness.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Chains.CoAdamek.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Chains.OmegaContPolynomialFunctors.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.
Local Open Scope functions.

Section MTypesAreSets.

  Context {A : ob HSET} (B : pr1hSet A → ob HSET).

  Local Definition F := MWithSets.F B.

  Lemma GetMType_HSET : Terminal (CoAlg_category (OmegaContPolynomialFunctors.F' B)).
  Proof.
    exact (limCoAlgTerminal TerminalHSET (PolyFunctor_omega_cont B) (LimConeHSET _ (termCochain TerminalHSET (OmegaContPolynomialFunctors.F' B)))).
  Defined.

  Lemma FinalCoalgAreSets (C : coalgebra F) (C_isfinal : is_final C) : isaset (pr1 C).
  Proof.
    set (C1'_t := GetMType_HSET).
    unfold Terminal in C1'_t.
    destruct C1'_t as [C1' C1'_isterm].
    set (C1 := MWithSets.C0 B C1').
    set (C1_isfinal := C0_is_final B C1' C1'_isterm : is_final C1).
    set (p := M_carriers_eq (pr1hSet A) (λ a, pr1hSet (B a)) (C1,, C1_isfinal) (C,, C_isfinal) : pr1 C1 = pr1 C).
    set (C1_isaset := pr21 C1' : isaset (pr1 C1)).
    apply (transportf (λ c, isaset c) p C1_isaset).
  Qed.

End MTypesAreSets.
