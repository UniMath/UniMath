(**

Shows global results that do not fit into a particular file but rather put the different strands together.
We focus on the results that are based on omega-cocontinuity (and not the existence of right Kan
extensions), which also explains the suffix "_alt" to the proper file name.

Written by Ralph Matthes, 2021
 *)

Set Kernel Term Sharing.


Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Section MainResult.


Context (C : category) (CP : BinCoproducts C).
Context (IC : Initial C) (CC : Colims_of_shape nat_graph C).

Local Notation "'EndC'":= ([C, C]) .
Local Notation "'Ptd'" := (category_Ptd C).

Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP.
Let EndEndC := [EndC, EndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC: BinCoproducts EndEndC.

Let InitialEndC : Initial EndC.
Proof.
apply Initial_functor_precat, IC.
Defined.

Let Colims_of_shape_nat_graph_EndC : Colims_of_shape nat_graph EndC.
Proof.
apply ColimsFunctorCategory_of_shape, CC.
Defined.

Context (H : functor [C, C] [C, C])
        (θ : StrengthForSignature H)
        (HH : is_omega_cocont H).

Let Const_plus_H (X : EndC) : functor EndC EndC
    := BinCoproduct_of_functors _ _ CPEndC (constant_functor _ _ X) H.

Let Id_H : functor [C, C] [C, C]
  := Const_plus_H (functor_identity _ : EndC).

Definition TermHSS : hss_category CP (Presignature_Signature (H,,θ)) :=
  InitHSS C CP IC CC (Presignature_Signature (H,,θ)) HH.

Definition TermHetSubst: heterogeneous_substitution C CP H
  := hetsubst_from_hss C CP (Presignature_Signature (H,,θ)) TermHSS.

Definition Terms: [C, C] := pr1 (pr1 TermHSS).
Definition TermAlgebra: FunctorAlg Id_H:= pr1 TermHSS.

Goal TermAlgebra = InitAlg C CP IC CC H HH.
Proof.
  apply idpath.
Qed.

Definition isInitialTermAlgebra: isInitial (FunctorAlg Id_H) TermAlgebra.
Proof.
  set (aux := colimAlgInitial InitialEndC (is_omega_cocont_Id_H C CP H HH) (Colims_of_shape_nat_graph_EndC _)).
  exact (pr2 aux).
Defined.

Definition TermMonad: Monad C := Monad_from_hss C CP (H,,θ) TermHSS.

Definition VarTerms: [C, C] ⟦ functor_identity C, Terms ⟧:= eta_from_alg TermAlgebra.

Definition ConstrTerms: [C, C] ⟦ H Terms, Terms ⟧ := tau_from_alg TermAlgebra.

Goal ConstrTerms = τ TermHetSubst.
Proof.
  apply idpath.
Qed.

Definition join: [C, C] ⟦ functor_compose _ _ _ Terms Terms, Terms ⟧ := prejoin_from_hetsubst TermHetSubst.

Goal join = μ TermMonad.
Proof.
  apply idpath.
Qed.

Definition joinLookup:
  ∏ c : C, pr1 VarTerms (pr1 Terms c) · pr1 join c = identity (pr1 Terms c)
  := @Monad_law1 C TermMonad.

Definition θforTerms := θ_from_hetsubst C CP H TermHetSubst Terms.

Goal θforTerms = PrecategoryBinProduct.nat_trans_fix_snd_arg_data [C, C] Ptd [C, C]
         (θ_source H) (θ_target H) (pr1 θ) (ptd_from_alg (InitAlg C CP IC CC H HH)) Terms.
Proof.
  apply idpath.
Qed.

Definition joinHomomorphic: θforTerms · # H join · ConstrTerms =
                  #(pre_composition_functor _ _ _ Terms) ConstrTerms  · join
  := prejoin_from_hetsubst_τ TermHetSubst.

Definition joinHasEtaLaw:
  ∏ c : C, # (pr1 Terms) (pr1 VarTerms c) · pr1 join c = identity (pr1 Terms c)
  := @Monad_law2 C TermMonad.

Definition joinHasPermutationLaw:
  ∏ c : C, # (pr1 Terms) (pr1 join c) · pr1 join c = pr1 join (pr1 Terms c) · pr1 join c
  := @Monad_law3 C TermMonad.


End MainResult.
