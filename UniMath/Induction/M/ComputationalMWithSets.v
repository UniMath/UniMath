(** ** Refinement of M-Types in the case of sets

    Author : Antoine Fisse (@AextraT), 2025

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.ComputationalM.
Require Import UniMath.Induction.M.MWithSets.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.

Section Upstream.

  Context {A : ob HSET} (B : pr1hSet A → ob HSET).

  Local Definition F := MWithSets.F B.
  Local Definition F' := MWithSets.F' B.

  Context (C0' : UniMath.CategoryTheory.FunctorCoalgebras.coalgebra_ob F') (C0'_is_final : isTerminal (UniMath.CategoryTheory.FunctorCoalgebras.CoAlg_category F') C0').

  Local Definition c0' : hSet :=  UniMath.CategoryTheory.FunctorCoalgebras.coalg_carrier F' C0'.

  Local Definition C0 : coalgebra F := MWithSets.C0 B C0'.
  Local Definition finalC0 : is_final C0 := MWithSets.C0_is_final B C0' C0'_is_final.

  Local Definition C : coalgebra F := ComputationalM.M (pr1 A) (λ a, pr1 (B a)) C0 finalC0.
  Local Definition finalC : is_final C := finalM (pr1 A) (λ a, pr1 (B a)) C0 finalC0.
  Local Definition c : type_precat := coalgebra_ob F C.
  Local Definition s_c := coalgebra_mor F C.

  Lemma c_isaset : isaset c.
  Proof.
    cbn.
    unfold carrierM.
    apply (isaset_total2_hSet c0' (λ m0, hProp_to_hSet (∃ (C : coalgebra F) (c : coalgebra_ob F C), (pr11 (finalC0 C)) c = m0))).
  Defined.

  Local Definition C' := MWithSets.C0' B C c_isaset.
  Local Definition finalC' := MWithSets.C0'_is_final B C c_isaset finalC.

  Local Definition corecC := ComputationalM.corecM (pr1 A) (λ a, pr1 (B a)) C0 finalC0.

  Lemma corec_computation_set C1 c1 : s_c (corecC C1 c1) = # F (corecC C1) (pr2 C1 c1).
  Proof.
    apply idpath.
  Defined.

End Upstream.
