(**

Instantiate the hypotheses of InitialHSS with Lam for HSET.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.

Section LamHSET.

Let Lam_S : Signature HSET has_homsets_HSET :=
  Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET BinProductsHSET.

Local Notation "'EndHSET'":= ([HSET, HSET, has_homsets_HSET]) .

Let hsEndC : has_homsets EndHSET := functor_category_has_homsets _ _ has_homsets_HSET.

Lemma Lam_Initial_HSET : Initial (precategory_FunctorAlg (Id_H _ _ CoproductsHSET Lam_S) hsEndC).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_coproduct_functor.
  + apply (BinProducts_functor_precat _ _ BinProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor; apply functor_category_has_homsets.
  + apply is_omega_cocont_Lam.
    * apply (has_exponentials_functor_HSET _ has_homsets_HSET).
    * apply cats_LimsHSET.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Lemma KanExt_HSET : ∀ Z : precategory_Ptd HSET has_homsets_HSET,
   RightKanExtension.GlobalRightKanExtensionExists HSET HSET
     (U Z) HSET has_homsets_HSET has_homsets_HSET.
Proof.
intro Z.
apply RightKanExtension_from_limits.
apply cats_LimsHSET.
Defined.

Definition LamHSS_Initial_HSET : Initial (hss_precategory CoproductsHSET Lam_S).
Proof.
apply InitialHSS.
- apply KanExt_HSET.
- apply Lam_Initial_HSET.
Defined.

Definition LamMonad : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply CoproductsHSET.
- apply Lam_S.
- apply LamHSS_Initial_HSET.
Defined.

End LamHSET.
