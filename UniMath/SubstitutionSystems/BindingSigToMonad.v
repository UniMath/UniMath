(**

Definition of binding signatures ([BindingSig]) and translation from from binding signatures to
monads ([BindingSigToMonad]). This is defined in multiple steps:

- Binding signature to a signature with strength ([BindingSigToSignature])
- Construction of initial algebra for a signature with strength ([SignatureInitialAlgebra])
- Signature with strength and initial algebra to a HSS ([SignatureToHSS])
- Construction of a monad from a HSS ([Monad_from_hss] in MonadsFromSubstitutionSystems.v)
- Composition of these maps to get a function from binding signatures to monads ([BindingSigToMonad])

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Combinatorics.Lists.

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
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.

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

(** A binding signature is a collection of lists of natural numbers indexed by types I *)
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

(** * Translation from a binding signature to a monad
<<
          S : BindingSig
      |-> functor(S) : functor [C,C] [C,C]
      |-> Initial (Id + functor(S))
      |-> I := Initial (HSS(func(S), θ)
      |-> M := Monad_from_HSS(I)
>>
*)
Section BindingSigToMonad.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "'C2'":= ([C, C, hsC]) .

Local Definition has_homsets_C2 : has_homsets C2.
Proof.
apply functor_category_has_homsets.
Defined.

(* TODO: Having limits and colimits should be sufficient *)
Context (BCC : BinCoproducts C) (BPC : BinProducts C)
        (IC : Initial C) (TC : Terminal C)
        (LC : Lims C) (CLC : Colims C).

Let optionC := (option_functor BCC TC).

(** Form "_ o option^n" and return Id if n = 0 *)
Definition precomp_option_iter (n : nat) : functor C2 C2.
Proof.
induction n as [|n IHn].
- apply functor_identity.
- apply (pre_composition_functor _ _ _ hsC _ (iter_functor1 _ optionC n)).
Defined.

Lemma is_omega_cocont_precomp_option_iter (n : nat) : is_omega_cocont (precomp_option_iter n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity has_homsets_C2).
- apply (is_omega_cocont_pre_composition_functor _ _ _ LC).
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
Definition Arity_to_Signature (xs : list nat) : Signature C hsC :=
 foldr1 (BinProduct_of_Signatures _ _ BPC) (IdSignature _ _)
        (map precomp_option_iter_Signature xs).

(** The H assumption follows directly if [C,C] has exponentials *)
Lemma is_omega_cocont_Arity_to_Signature (xs : list nat)
  (H : Π (x : C2), is_omega_cocont (constprod_functor1 (BinProducts_functor_precat _ _ BPC hsC) x)) :
  is_omega_cocont (Arity_to_Signature xs).
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
    * intro x; apply (H x).
Defined.

(** ** Binding signature to a signature with strength *)
Definition BindingSigToSignature (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
  Signature C hsC.
Proof.
apply (Sum_of_Signatures (BindingSigIndex sig)).
- apply CC.
- intro i; apply (Arity_to_Signature (BindingSigMap sig i)).
Defined.

Lemma is_omega_cocont_BindingSigToSignature (sig : BindingSig)
  (CC : Coproducts (BindingSigIndex sig) C) (PC : Products (BindingSigIndex sig) C)
  (H : Π (x : C2), is_omega_cocont (constprod_functor1 (BinProducts_functor_precat _ _ BPC hsC) x)) :
  is_omega_cocont (BindingSigToSignature sig CC).
Proof.
apply (is_omega_cocont_Sum_of_Signatures _ (BindingSigIsdeceq sig)).
- intro i; apply is_omega_cocont_Arity_to_Signature, H.
- apply PC.
Defined.

(** ** Construction of initial algebra for a signature with strength *)
Definition SignatureInitialAlgebra (s : Signature C hsC) (Hs : is_omega_cocont s) :
  Initial (FunctorAlg (Id_H C hsC BCC s) has_homsets_C2).
Proof.
use colimAlgInitial.
- apply (Initial_functor_precat _ _ IC).
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_BinCoproduct_of_functors.
  + apply (BinProducts_functor_precat _ _ BPC).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor, functor_category_has_homsets.
  + apply Hs.
- apply ColimsFunctorCategory; apply CLC.
Defined.

(** ** Signature with strength and initial algebra to a HSS *)
Definition SignatureToHSS (s : Signature C hsC)
  (Hs : Initial (FunctorAlg (Id_H C hsC BCC s) has_homsets_C2)) :
  hss_precategory BCC s.
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, LC.
- apply Hs.
Defined.

(** The above HSS is initial *)
Definition SignatureToHSSisInitial (s : Signature C hsC)
  (Hs : Initial (FunctorAlg (Id_H C hsC BCC s) has_homsets_C2)) :
  isInitial _ (SignatureToHSS s Hs).
Proof.
now unfold SignatureToHSS; destruct InitialHSS.
Qed.

(** ** Function from binding signatures to monads *)
Definition BindingSigToMonad (sig : BindingSig)
  (CC : Coproducts (BindingSigIndex sig) C) (PC : Products (BindingSigIndex sig) C)
  (H : Π (x : C2), is_omega_cocont (constprod_functor1 (BinProducts_functor_precat _ _ BPC hsC) x)) :
  Monad C.
Proof.
use (Monad_from_hss _ hsC BCC).
- apply (BindingSigToSignature sig CC).
- apply SignatureToHSS.
  apply SignatureInitialAlgebra.
  apply (is_omega_cocont_BindingSigToSignature _ _ PC H).
Defined.

End BindingSigToMonad.

(** * Specialized versions of some of the above functions for HSET *)
Section BindingSigToMonadHSET.

Local Definition has_homsets_HSET2 : has_homsets [HSET,HSET,has_homsets_HSET].
Proof.
apply functor_category_has_homsets.
Defined.

(** ** Binding signature to signature with strength for HSET *)
Definition BindingSigToSignatureHSET (sig : BindingSig) : Signature HSET has_homsets_HSET.
Proof.
use BindingSigToSignature.
- apply BinCoproductsHSET.
- apply BinProductsHSET.
- apply TerminalHSET.
- apply sig.
- apply Coproducts_HSET, (isasetifdeceq _ (BindingSigIsdeceq sig)).
Defined.

Lemma is_omega_cocont_BindingSigToSignatureHSET (sig : BindingSig) :
  is_omega_cocont (BindingSigToSignatureHSET sig).
Proof.
apply (is_omega_cocont_Sum_of_Signatures _ (BindingSigIsdeceq sig)).
- intro i; apply is_omega_cocont_Arity_to_Signature.
  + apply LimsHSET.
  + intros F.
    apply (is_omega_cocont_constprod_functor1 _ has_homsets_HSET2).
    apply has_exponentials_functor_HSET, has_homsets_HSET.
- apply Products_HSET.
Defined.

(** ** Construction of initial algebra for a signature with strength for HSET *)
Definition SignatureInitialAlgebraHSET (s : Signature HSET has_homsets_HSET) (Hs : is_omega_cocont s) :
  Initial (FunctorAlg (Id_H _ _ BinCoproductsHSET s) has_homsets_HSET2).
Proof.
apply SignatureInitialAlgebra.
- apply BinProductsHSET.
- apply InitialHSET.
- apply ColimsHSET.
- apply Hs.
Defined.

(** ** Binding signature to a monad for HSET *)
Definition BindingSigToMonadHSET (sig : BindingSig) : Monad HSET.
Proof.
use (BindingSigToMonad _ _ _ _ _ _ _ sig).
- apply has_homsets_HSET.
- apply BinCoproductsHSET.
- apply BinProductsHSET.
- apply InitialHSET.
- apply TerminalHSET.
- apply LimsHSET.
- apply ColimsHSET.
- apply Coproducts_HSET.
  exact (isasetifdeceq _ (BindingSigIsdeceq sig)).
- apply Products_HSET.
- intros F.
  apply (is_omega_cocont_constprod_functor1 _ has_homsets_HSET2).
  apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

End BindingSigToMonadHSET.



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
