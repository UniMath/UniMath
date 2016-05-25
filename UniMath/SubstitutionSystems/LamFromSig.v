(**

Obtain the lambda calculus from the signature [[0,0],[1]]

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.ProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial.

Section Lam.

Infix "::" := (cons_list nat).
Notation "[]" := (nil_list nat) (at level 0, format "[]").

Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Local Definition ProductsHSET2 : Products HSET2.
Proof.
apply (Products_functor_precat _ _ ProductsHSET).
Defined.

Local Definition CoproductsHSET2 : Coproducts HSET2.
Proof.
apply (Coproducts_functor_precat _ _ CoproductsHSET).
Defined.

Local Lemma has_exponentials_HSET2 : has_exponentials ProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

Local Lemma InitialHSET2 : Initial HSET2.
Proof.
apply (Initial_functor_precat _ _ InitialHSET).
Defined.

(* The signature of the lambda calculus: [[0,0],[1]] *)
Definition LamSig : Sig :=
  cons_list (list nat) (0 :: 0 :: [])
   (cons_list (list nat) (1 :: []) (nil_list (list nat))).

Local Notation "'Id'" := (functor_identity _).

Local Notation "F * G" := (H HSET has_homsets_HSET ProductsHSET F G).

Local Notation "F + G" := (SumOfSignatures.H _ _ CoproductsHSET F G).
Local Notation "'_' 'o' 'option'" :=
  (ℓ (option_functor HSET CoproductsHSET TerminalHSET)) (at level 0).

Eval cbn in pr1 (SigToSignature LamSig).
(* = Id * Id + _ o option *)
(*      : functor [HSET, HSET, has_homsets_HSET] *)
(*          [HSET, HSET, has_homsets_HSET] *)

Require Import UniMath.SubstitutionSystems.LamHSET.

Let Lam_S : Signature HSET has_homsets_HSET :=
  Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET ProductsHSET.

Goal (pr1 Lam_S = pr1 (SigToSignature LamSig)).
now apply idpath.
Abort.

Definition LamSignature : Signature HSET has_homsets_HSET := SigToSignature LamSig.
Definition LamFunctor : functor HSET2 HSET2 := Id_H _ _ CoproductsHSET LamSignature.

Definition LamMonad : Monad HSET := SigToMonad LamSig.

(* Definition lambdaOmegaFunctor : omega_cocont_functor HSET2 HSET2 := *)
(*   '(functor_identity HSET) + (Id * Id + _ o option). *)

(* Let lambdaFunctor : functor HSET2 HSET2 := pr1 LamSignature. *)
(* Let is_omega_cocont_lambdaFunctor : is_omega_cocont lambdaFunctor := *)
(*   pr2 lambdaOmegaFunctor. *)

Lemma lambdaFunctor_Initial :
   Initial (FunctorAlg LamFunctor has_homsets_HSET2).
Proof.
apply (SigInitial LamSig).
Defined.

Definition LC : HSET2 :=
  alg_carrier _ (InitialObject lambdaFunctor_Initial).

Let LC_mor : HSET2⟦LamFunctor LC,LC⟧ :=
  alg_map _ (InitialObject lambdaFunctor_Initial).

Let LC_alg : algebra_ob LamFunctor :=
  InitialObject lambdaFunctor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,LC⟧ :=
  CoproductIn1 HSET2 _ ;; LC_mor.

(* How to do this nicer? *)
Definition prod2 (x y : HSET2) : HSET2.
Proof.
apply ProductsHSET2; [apply x | apply y].
Defined.

Definition app_map : HSET2⟦prod2 LC LC,LC⟧ :=
  CoproductIn1 HSET2 _ ;; CoproductIn2 HSET2 _ ;; LC_mor.

Definition app_map' (x : HSET) : HSET⟦(pr1 LC x × pr1 LC x)%set,pr1 LC x⟧.
Proof.
apply app_map.
Defined.

Let precomp_option X := (pre_composition_functor _ _ HSET has_homsets_HSET has_homsets_HSET
                  (option_functor HSET CoproductsHSET TerminalHSET) X).

Definition lam_map : HSET2⟦precomp_option LC,LC⟧ :=
  CoproductIn2 HSET2 _ ;; CoproductIn2 HSET2 _ ;; LC_mor.

Definition mk_lambdaAlgebra (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : algebra_ob LamFunctor.
Proof.
apply (tpair _ X).
simple refine (CoproductArrow _ _ fvar (CoproductArrow _ _ fapp flam)).
Defined.

Definition foldr_map (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  algebra_mor _ LC_alg (mk_lambdaAlgebra X fvar fapp flam).
Proof.
apply (InitialArrow lambdaFunctor_Initial (mk_lambdaAlgebra X fvar fapp flam)).
Defined.

End Lam.
