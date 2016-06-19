(**

From signatures to monads

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
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
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
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
Section SigToMonad.

Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Definition BinProductsHSET2 : BinProducts HSET2.
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Definition BinCoproductsHSET2 : BinCoproducts HSET2.
Proof.
apply (BinCoproducts_functor_precat _ _ BinCoproductsHSET).
Defined.

Lemma has_exponentials_HSET2 : has_exponentials BinProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

Definition Sig : UU := list (list nat).

Let optionHSET := (option_functor HSET BinCoproductsHSET TerminalHSET).

(* Form "_ o option^n" and return Id if n = 0 *)
Definition precomp_option_iter (n : nat) : functor HSET2 HSET2 := match n with
  | O => functor_identity HSET2
  | S n => pre_composition_functor _ _ _ has_homsets_HSET _ (iter_functor1 _ optionHSET n)
  end.

Lemma is_omega_cocont_precomp_option_iter (n : nat) : is_omega_cocont (precomp_option_iter n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- apply (is_omega_cocont_pre_composition_functor _ _ _ (iter_functor1 _ optionHSET n) _ _ cats_LimsHSET).
Defined.

Definition precomp_option_iter_Signature (n : nat) : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply (precomp_option_iter n).
- destruct n; simpl.
  + apply (θ_functor_identity HSET).
  + set (F := δ_iter_functor1 _ _ _ (δ_option _ has_homsets_HSET TerminalHSET BinCoproductsHSET)).
    apply (θ_precompG _ has_homsets_HSET (iter_functor1 HSET optionHSET n) (F n)).
    * apply δ_law1_iter_functor1, δ_law1_option.
    * apply δ_law2_iter_functor1, δ_law2_option.
Defined.

(* [nat] to a Signature *)
Definition Arity_to_Signature : list nat -> Signature HSET has_homsets_HSET.
Proof.
intros xs.
generalize (map_list precomp_option_iter_Signature xs).
apply foldr1_list.
- apply (BinProduct_of_Signatures _ _ BinProductsHSET).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_Arity_to_Signature (xs : list nat) : is_omega_cocont (Arity_to_Signature xs).
Proof.
destruct xs as [n xs].
destruct n.
- destruct xs; simpl; apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- induction n.
  + destruct xs as [m []]; simpl.
    apply is_omega_cocont_precomp_option_iter.
  + destruct xs as [m xs].
    generalize (IHn xs).
    destruct xs.
    intro IH.
    apply is_omega_cocont_BinProduct_of_Signatures.
    apply is_omega_cocont_precomp_option_iter.
    apply IH.
    apply has_exponentials_HSET2.
Defined.

(* [[nat]] to Signature *)
Definition SigToSignature : Sig -> Signature HSET has_homsets_HSET.
Proof.
intro xs.
generalize (map_list Arity_to_Signature xs).
apply foldr1_list.
- apply (BinSum_of_Signatures _ _ BinCoproductsHSET).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_SigToSignature (s : Sig) : is_omega_cocont (SigToSignature s).
Proof.
destruct s as [n xs].
destruct n.
- destruct xs.
  apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- induction n.
  + destruct xs as [xs []]; simpl.
    apply is_omega_cocont_Arity_to_Signature.
  + destruct xs as [m xs].
    generalize (IHn xs).
    destruct xs.
    intro IH.
    apply is_omega_cocont_BinSum_of_Signatures.
    apply is_omega_cocont_Arity_to_Signature.
    apply IH.
    apply BinProductsHSET.
Defined.

Definition SigInitial (sig : Sig) :
  Initial (FunctorAlg (Id_H HSET has_homsets_HSET BinCoproductsHSET (SigToSignature sig)) has_homsets_HSET2).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_bincoproduct_of_functors.
  + apply (BinProducts_functor_precat _ _ BinProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor, functor_category_has_homsets.
  + apply is_omega_cocont_SigToSignature.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Definition SigInitialHSS (sig : Sig) :
  Initial (hss_precategory BinCoproductsHSET (SigToSignature sig)).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, cats_LimsHSET.
- apply SigInitial.
Defined.

Definition SigToMonad (sig : Sig) : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply BinCoproductsHSET.
- apply (SigToSignature sig).
- apply SigInitialHSS.
Defined.

End SigToMonad.
