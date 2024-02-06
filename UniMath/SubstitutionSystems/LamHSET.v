(**

Instantiate the hypotheses of InitialHSS with Lam for HSET.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Chains.All.

Section LamHSET.

Let Lam_S : Signature HSET _ _ :=
  Lam_Sig HSET TerminalHSET BinCoproductsHSET BinProductsHSET.

Local Notation "'EndHSET'":= ([HSET, HSET]) .

Local Lemma is_omega_cocont_Lam_S : is_omega_cocont Lam_S.
Proof.
apply is_omega_cocont_Lam.
* apply is_omega_cocont_constprod_functor1.
  apply Exponentials_functor_HSET.
* apply ColimsHSET_of_shape.
Defined.

Lemma Lam_Initial_HSET : Initial (category_FunctorAlg (Id_H _ BinCoproductsHSET Lam_S)).
Proof.
use colimAlgInitial.
- apply (Initial_functor_precat _ _ InitialHSET).
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_BinCoproduct_of_functors.
  + apply is_omega_cocont_constant_functor.
  + apply is_omega_cocont_Lam_S.
- apply ColimsFunctorCategory_of_shape; apply ColimsHSET_of_shape.
Defined.

(* Lemma KanExt_HSET : ∏ Z : precategory_Ptd HSET has_homsets_HSET, *)
(*    RightKanExtension.GlobalRightKanExtensionExists HSET HSET *)
(*      (U Z) HSET has_homsets_HSET has_homsets_HSET. *)
(* Proof. *)
(* intro Z. *)
(* apply RightKanExtension_from_limits, LimsHSET. *)
(* Defined. *)

Definition LamHSS_Initial_HSET : Initial (hss_category BinCoproductsHSET Lam_S).
Proof.
apply InitialHSS.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_Lam_S.
Defined.

Definition LamMonad : Monad HSET.
Proof.
use Monad_from_hss.
- apply BinCoproductsHSET.
- apply Lam_S.
- apply LamHSS_Initial_HSET.
Defined.

End LamHSET.
