(**

From general signatures to monads. A general signature is a collection
of lists of natural numbers indexed by a type I with decidable
equality:

Definition GenSig : UU := I -> list nat.


Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "'HSET2'":= ([HSET, HSET, has_homsets_HSET]) .

(* Translation from a Sig to a monad by: *)
(* S : SIG *)
(* |-> *)
(* functor(S) : functor [Set,Set] [Set,Set] *)
(* |-> *)
(* Initial (Id + functor(S)) *)
(* |-> *)
(* I:= Initial (HSS(func(S), \theta) *)
(* |-> *)
(* M := Monad_from_HSS(I)    # *)
Section GenSigToMonad.

Definition GenSig : UU := Σ (I : UU), Σ (h : isdeceq I), I -> list nat.

Definition GenSigIndex : GenSig -> UU := pr1.
Definition GenSigIsdeceq (s : GenSig) : isdeceq (GenSigIndex s) :=
  pr1 (pr2 s).
Definition GenSigMap (s : GenSig) : GenSigIndex s -> list nat :=
  pr2 (pr2 s).

Definition mkGenSig {I : UU} (h : isdeceq I) (f : I -> list nat) : GenSig :=
  tpair _ I (tpair _ h f).

Definition SumGenSig : GenSig -> GenSig -> GenSig.
Proof.
intros s1 s2.
mkpair.
- apply (GenSigIndex s1 ⨿ GenSigIndex s2).
- mkpair.
  + apply (isdeceqcoprod (GenSigIsdeceq s1) (GenSigIsdeceq s2)).
  + induction 1 as [i|i]; [ apply (GenSigMap s1 i) | apply (GenSigMap s2 i) ].
Defined.

Variable (sig : GenSig).
Let I := GenSigIndex sig.
Let HI := GenSigIsdeceq sig.

Definition GenSigToSignature : Signature HSET has_homsets_HSET.
Proof.
eapply (Sum_of_Signatures I).
- apply Coproducts_HSET, (isasetifdeceq _ HI).
- intro i; apply (Arity_to_Signature (GenSigMap sig i)).
Defined.

Lemma is_omega_cocont_GenSigToSignature : is_omega_cocont GenSigToSignature.
Proof.
apply (is_omega_cocont_Sum_of_Signatures _ HI).
- intro i; apply is_omega_cocont_Arity_to_Signature.
- apply Products_HSET.
Defined.

Definition GenSigInitial :
  Initial (FunctorAlg (Id_H HSET has_homsets_HSET BinCoproductsHSET
                        GenSigToSignature) has_homsets_HSET2).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_BinCoproduct_of_functors.
  + apply (BinProducts_functor_precat _ _ BinProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor, functor_category_has_homsets.
  + apply is_omega_cocont_GenSigToSignature.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Definition GenSigInitialHSS : Initial (hss_precategory BinCoproductsHSET GenSigToSignature).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, cats_LimsHSET.
- apply GenSigInitial.
Defined.

Definition GenSigToMonad : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply BinCoproductsHSET.
- apply GenSigToSignature.
- apply GenSigInitialHSS.
Defined.

End GenSigToMonad.
