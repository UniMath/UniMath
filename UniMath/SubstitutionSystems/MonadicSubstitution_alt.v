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


Context (C : precategory) (hsC : has_homsets C) (CP : BinCoproducts C).
Context (IC : Initial C) (CC : Colims_of_shape nat_graph C).

Local Notation "'EndC'":= ([C, C, hsC]) .
Local Notation "'Ptd'" := (precategory_Ptd C hsC).

Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hsC.
Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP hsC.
Let EndEndC := [EndC, EndC, hsEndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC hsEndC: BinCoproducts EndEndC.

Let InitialEndC : Initial EndC.
Proof.
apply Initial_functor_precat, IC.
Defined.

Let Colims_of_shape_nat_graph_EndC : Colims_of_shape nat_graph EndC.
Proof.
apply ColimsFunctorCategory_of_shape, CC.
Defined.

Context (H : functor [C, C, hsC] [C, C, hsC])
        (θ : StrengthForSignature(hs:=hsC) H)
        (HH : is_omega_cocont H).

Let Const_plus_H (X : EndC) : functor EndC EndC
    := BinCoproduct_of_functors _ _ CPEndC (constant_functor _ _ X) H.

Let Id_H : functor [C, C, hsC] [C, C, hsC]
  := Const_plus_H (functor_identity _ : EndC).

Definition TermHSS : hss_precategory CP (Presignature_Signature (H,,θ)) :=
  InitHSS C hsC CP IC CC (Presignature_Signature (H,,θ)) HH.

Definition Terms: [C, C, hsC] := pr1 (pr1 TermHSS).
Definition TermAlgebra: FunctorAlg Id_H hsEndC:= pr1 TermHSS.

Goal TermAlgebra = InitAlg C hsC CP IC CC H HH.
Proof.
  apply idpath.
Qed.

Definition isInitialTermAlgebra: isInitial (FunctorAlg Id_H hsEndC) TermAlgebra.
Proof.
  set (aux := colimAlgInitial hsEndC InitialEndC (is_omega_cocont_Id_H C hsC CP H HH) (Colims_of_shape_nat_graph_EndC _)).
  exact (pr2 aux).
Defined.

Definition TermMonad: Monad C := Monad_from_hss C hsC CP (H,,θ) TermHSS.

Definition join: functor_composite Terms Terms ⟹ pr1 Terms := prejoin_from_hetsubst (hetsubst_from_hss C hsC CP (Presignature_Signature (H,,θ)) TermHSS).

Goal join = μ TermMonad.
Proof.
  apply idpath.
Qed.

End MainResult.
