(**

Obtain the lambda calculus from the signature [[0,0],[1]]

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.ProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.

Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.

Section Lam.

Infix "::" := (cons_list nat).
Notation "[]" := (nil_list nat) (at level 0, format "[]").

(* The signature of the lambda calculus: [[0,0],[1]] *)
Definition LamSig : Sig := cons_list (list nat) (0 :: 0 :: []) (cons_list (list nat) (1 :: []) (nil_list (list nat))).

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

Definition LamMonad : Monad HSET := SigToMonad LamSig.

End Lam.
