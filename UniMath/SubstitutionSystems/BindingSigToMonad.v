(**

Definition of binding signatures ([BindingSig]) and translation from from binding signatures to
monads ([BindingSigToMonad]).

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.Inductives.Lists.
Require Import UniMath.CategoryTheory.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(** * Definition of binding signatures *)
Section BindingSig.

(** A binding signature is a collection of lists of natural numbers indexed by types I. *)
Definition BindingSig : UU := Σ (I : UU) (h : isdeceq I), I -> list nat.

Definition BindingSigIndex : BindingSig -> UU := pr1.
Definition BindingSigIsdeceq (s : BindingSig) : isdeceq (BindingSigIndex s) :=
  pr1 (pr2 s).
Definition BindingSigMap (s : BindingSig) : BindingSigIndex s -> list nat :=
  pr2 (pr2 s).

Definition mkBindingSig {I : UU} (h : isdeceq I) (f : I -> list nat) : BindingSig := (I,,h,,f).

(** Sum of binding signatures *)
Definition SumBindingSig : BindingSig -> BindingSig -> BindingSig.
Proof.
intros s1 s2.
mkpair.
- apply (BindingSigIndex s1 ⨿ BindingSigIndex s2).
- mkpair.
  + apply (isdeceqcoprod (BindingSigIsdeceq s1) (BindingSigIsdeceq s2)).
  + induction 1 as [i|i]; [ apply (BindingSigMap s1 i) | apply (BindingSigMap s2 i) ].
Defined.

End BindingSig.

(** * Translation from a binding signature to a monad by:
<<
          S : BindingSig
      |-> functor(S) : functor [Set,Set] [Set,Set]
      |-> Initial (Id + functor(S))
      |-> I := Initial (HSS(func(S), θ)
      |-> M := Monad_from_HSS(I)
>>
*)
Section BindingSigToMonad.

Context (sig : BindingSig) {C : precategory} (hsC : has_homsets C).

Let I := BindingSigIndex sig.
Let HI := BindingSigIsdeceq sig.
Local Notation "'C2'":= ([C, C, hsC]) .

Context (BCC : BinCoproducts C) (CC : Coproducts I C)
        (BPC : BinProducts C) (PC : Products I C)
        (IC : Initial C) (TC : Terminal C) (LC : Lims C) (CLC : Colims C).

Context (EC2 : has_exponentials (BinProducts_functor_precat C C BPC hsC)).

Let optionC := (option_functor C BCC TC).

Definition has_homsets_C2 : has_homsets C2.
Proof.
apply functor_category_has_homsets.
Defined.

(** Form "_ o option^n" and return Id if n = 0 *)
Definition precomp_option_iter (n : nat) : functor C2 C2 := match n with
  | O => functor_identity C2
  | S n => pre_composition_functor _ _ _ hsC _ (iter_functor1 _ optionC n)
  end.

Lemma is_omega_cocont_precomp_option_iter (n : nat) : is_omega_cocont (precomp_option_iter n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity has_homsets_C2).
- apply (is_omega_cocont_pre_composition_functor (iter_functor1 _ optionC n) _ _ LC).
Defined.

Definition precomp_option_iter_Signature (n : nat) : Signature C hsC.
Proof.
mkpair.
- apply (precomp_option_iter n).
- destruct n; simpl.
  + apply θ_functor_identity.
  + set (F := δ_iter_functor1 _ _ _ (δ_option _ hsC TC BCC)).
    apply (θ_precompG _ hsC (iter_functor1 _ optionC n) (F n)).
    * apply δ_law1_iter_functor1, δ_law1_option.
    * apply δ_law2_iter_functor1, δ_law2_option.
Defined.

(** [nat] to a Signature *)
Definition Arity_to_Signature : list nat -> Signature C hsC.
Proof.
intros xs.
generalize (map_list precomp_option_iter_Signature xs).
apply foldr1_list.
- apply (BinProduct_of_Signatures _ _ BPC).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_Arity_to_Signature (xs : list nat) : is_omega_cocont (Arity_to_Signature xs).
Proof.
destruct xs as [[|n] xs].
- destruct xs; apply (is_omega_cocont_functor_identity has_homsets_C2).
- induction n as [|n IHn].
  + destruct xs as [m []]; simpl.
    apply is_omega_cocont_precomp_option_iter.
  + destruct xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_Signatures.
    * apply is_omega_cocont_precomp_option_iter.
    * apply (IHn (k,,xs)).
    * apply is_omega_cocont_constprod_functor1;
        [ apply has_homsets_C2 | apply EC2 ].
Defined.

Definition BindingSigToSignature : Signature C hsC.
Proof.
apply (Sum_of_Signatures I).
- apply CC.
- intro i; apply (Arity_to_Signature (BindingSigMap sig i)).
Defined.

Lemma is_omega_cocont_BindingSigToSignature : is_omega_cocont BindingSigToSignature.
Proof.
apply (is_omega_cocont_Sum_of_Signatures _ HI).
- intro i; apply is_omega_cocont_Arity_to_Signature.
- apply PC.
Defined.

Definition BindingSigInitial :
  Initial (FunctorAlg (Id_H C hsC BCC BindingSigToSignature) has_homsets_C2).
Proof.
use colimAlgInitial.
- apply (Initial_functor_precat _ _ IC).
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_BinCoproduct_of_functors.
  + apply (BinProducts_functor_precat _ _ BPC).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor, functor_category_has_homsets.
  + apply is_omega_cocont_BindingSigToSignature.
- apply ColimsFunctorCategory; apply CLC.
Defined.

Definition BindingSigInitialHSS : Initial (hss_precategory BCC BindingSigToSignature).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, LC.
- apply BindingSigInitial.
Defined.

Definition BindingSigToMonad : Monad C.
Proof.
use Monad_from_hss.
- apply hsC.
- apply BCC.
- apply BindingSigToSignature.
- apply BindingSigInitialHSS.
Defined.

End BindingSigToMonad.


(* Old code for translation from lists of lists *)

(* (* [[nat]] to Signature *) *)
(* Definition SigToSignature : Sig -> Signature HSET has_homsets_HSET. *)
(* Proof. *)
(* intro xs. *)
(* generalize (map_list Arity_to_Signature xs). *)
(* apply foldr1_list. *)
(* - apply (BinSum_of_Signatures _ _ BinCoproductsHSET). *)
(* - apply IdSignature. *)
(* Defined. *)

(* Lemma is_omega_cocont_SigToSignature (s : Sig) : is_omega_cocont (SigToSignature s). *)
(* Proof. *)
(* destruct s as [n xs]. *)
(* destruct n. *)
(* - destruct xs. *)
(*   apply (is_omega_cocont_functor_identity has_homsets_HSET2). *)
(* - induction n. *)
(*   + destruct xs as [xs []]; simpl. *)
(*     apply is_omega_cocont_Arity_to_Signature. *)
(*   + destruct xs as [m xs]. *)
(*     generalize (IHn xs). *)
(*     destruct xs. *)
(*     intro IH. *)
(*     apply is_omega_cocont_BinSum_of_Signatures. *)
(*     apply is_omega_cocont_Arity_to_Signature. *)
(*     apply IH. *)
(*     apply BinProductsHSET. *)
(* Defined. *)

(* TODO: Add special function for HSET *)