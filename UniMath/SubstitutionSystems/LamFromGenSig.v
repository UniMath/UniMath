(**

Obtain the lambda calculus from the signature { [0,0], [1] }

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
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.arbitrary_products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseArbitraryProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseArbitraryCoproduct.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.ArbitrarySumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.
Require Import UniMath.SubstitutionSystems.GenSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial.

Section GenLam.

Infix "::" := (cons_list nat).
Notation "[]" := (nil_list nat) (at level 0, format "[]").

Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Local Definition BinProductsHSET2 : BinProducts HSET2.
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Local Definition ArbitraryProductsHSET2 : ArbitraryProducts bool HSET2.
Proof.
apply (ArbitraryProducts_functor_precat _ _ _ (ArbitraryProducts_HSET bool)).
Defined.

Local Definition BinCoproductsHSET2 : BinCoproducts HSET2.
Proof.
apply (BinCoproducts_functor_precat _ _ BinCoproductsHSET).
Defined.

Local Lemma has_exponentials_HSET2 : has_exponentials BinProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

Local Lemma InitialHSET2 : Initial HSET2.
Proof.
apply (Initial_functor_precat _ _ InitialHSET).
Defined.

(* The signature of the lambda calculus: { [0,0], [1] } *)
Definition GenLamSig : GenSig :=
  mkGenSig isdeceqbool (fun b => if b then 0 :: 0 :: [] else 1 :: []).

Local Notation "'Id'" := (functor_identity _).

Local Notation "F * G" := (H HSET has_homsets_HSET BinProductsHSET F G).

Local Notation "F + G" := (BinSumOfSignatures.H _ _ BinCoproductsHSET F G).
Local Notation "'_' 'o' 'option'" :=
  (ℓ (option_functor HSET BinCoproductsHSET TerminalHSET)) (at level 10).

Definition GenLamSignature : Signature HSET has_homsets_HSET := GenSigToSignature GenLamSig.
Definition GenLamFunctor : functor HSET2 HSET2 := Id_H _ _ BinCoproductsHSET GenLamSignature.

Definition GenLamMonad : Monad HSET := GenSigToMonad GenLamSig.

(* From here on it is exactly the same as in CT/lambdacalculus.v *)
Lemma lambdaFunctor_Initial :
   Initial (FunctorAlg GenLamFunctor has_homsets_HSET2).
Proof.
apply (GenSigInitial GenLamSig).
Defined.

Definition LC : HSET2 :=
  alg_carrier _ (InitialObject lambdaFunctor_Initial).

Let LC_mor : HSET2⟦GenLamFunctor LC,LC⟧ :=
  alg_map _ (InitialObject lambdaFunctor_Initial).

Let LC_alg : algebra_ob GenLamFunctor :=
  InitialObject lambdaFunctor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,LC⟧ :=
  BinCoproductIn1 HSET2 _ ;; LC_mor.

(* How to do this nicer? *)
Definition prod2 (x y : HSET2) : HSET2.
Proof.
apply BinProductsHSET2; [apply x | apply y].
Defined.

Definition app_map : HSET2⟦prod2 LC LC,LC⟧ :=
  ArbitraryCoproductIn bool HSET2 _ true ;; BinCoproductIn2 HSET2 _ ;; LC_mor.

Definition app_map' (x : HSET) : HSET⟦(pr1 LC x × pr1 LC x)%set,pr1 LC x⟧.
Proof.
apply app_map.
Defined.

Let precomp_option X := (pre_composition_functor _ _ HSET has_homsets_HSET has_homsets_HSET
                  (option_functor HSET BinCoproductsHSET TerminalHSET) X).

Definition lam_map : HSET2⟦precomp_option LC,LC⟧ :=
  ArbitraryCoproductIn bool HSET2 _ false ;; BinCoproductIn2 HSET2 _ ;; LC_mor.

Definition mk_lambdaAlgebra (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : algebra_ob GenLamFunctor.
Proof.
apply (tpair _ X).
simple refine (BinCoproductArrow _ _ fvar _).
simple refine (ArbitraryCoproductArrow _ _ _ _).
intro b; destruct b.
- apply fapp.
- apply flam.
Defined.

Definition foldr_map (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  algebra_mor GenLamFunctor LC_alg (mk_lambdaAlgebra X fvar fapp flam).
Proof.
apply (InitialArrow lambdaFunctor_Initial (mk_lambdaAlgebra X fvar fapp flam)).
Defined.

Definition foldr_map' (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
   HSET2 ⟦ pr1 LC_alg, pr1 (mk_lambdaAlgebra X fvar fapp flam) ⟧.
Proof.
apply (foldr_map X fvar fapp flam).
Defined.

Lemma foldr_var (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  var_map ;; foldr_map X fvar fapp flam = fvar.
Proof.
assert (F := maponpaths (fun x => BinCoproductIn1 _ _ ;; x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
apply id_left.
Defined.

Lemma foldr_app (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  app_map ;; foldr_map X fvar fapp flam =
  # (pr1 (Id * Id)) (foldr_map X fvar fapp flam) ;; fapp.
Proof.
assert (F := maponpaths (fun x => ArbitraryCoproductIn _ _ _ true ;; BinCoproductIn2 _ _ ;; x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, cancel_postcomposition.
  apply (ArbitraryCoproductOfArrowsIn _ _ (ArbitraryCoproducts_functor_precat _ _ _
          (ArbitraryCoproducts_HSET _ (isasetifdeceq _ isdeceqbool))
          _ (λ i, pr1 (Arity_to_Signature (GenSigMap GenLamSig i)) `LC_alg))).
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|].
rewrite <- assoc.
eapply pathscomp0; eapply maponpaths.
  refine (ArbitraryCoproductInCommutes _ _ _ _ _ _ true).
apply idpath.
Defined.

Lemma foldr_lam (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  lam_map ;; foldr_map X fvar fapp flam =
  # (pr1 (_ o option)) (foldr_map X fvar fapp flam) ;; flam.
Proof.
assert (F := maponpaths (fun x => ArbitraryCoproductIn _ _ _ false ;; BinCoproductIn2 _ _ ;; x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, cancel_postcomposition.
  apply (ArbitraryCoproductOfArrowsIn _ _ (ArbitraryCoproducts_functor_precat _ _ _
          (ArbitraryCoproducts_HSET _ (isasetifdeceq _ isdeceqbool))
          _ (λ i, pr1 (Arity_to_Signature (GenSigMap GenLamSig i)) `LC_alg))).
rewrite <- assoc.
eapply pathscomp0.
  eapply maponpaths, BinCoproductIn2Commutes.
rewrite <- assoc.
eapply pathscomp0; eapply maponpaths.
  refine (ArbitraryCoproductInCommutes _ _ _ _ _ _ false).
apply idpath.
Defined.

End GenLam.
