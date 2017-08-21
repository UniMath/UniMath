(**

Definition of binding signatures ([BindingSig]) and translation from from binding signatures to
monads ([BindingSigToMonad]). This is defined in multiple steps:

- Binding signature to a signature with strength ([BindingSigToSignature])
- Construction of initial algebra for a signature with strength ([SignatureInitialAlgebra])
- Signature with strength and initial algebra to a HSS ([SignatureToHSS])
- Construction of a monad from a HSS ([Monad_from_hss] in MonadsFromSubstitutionSystems.v)
- Composition of these maps to get a function from binding signatures to monads ([BindingSigToMonad])

Written by: Anders Mörtberg, 2016
-
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
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
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope cat.

Local Notation "[ C , D , hsD ]" := (functor_precategory C D hsD).
Local Notation "'chain'" := (diagram nat_graph).

(** * Definition of binding signatures *)
Section BindingSig.

(** A binding signature is a collection of lists of natural numbers indexed by types I *)
Definition BindingSig : UU := ∑ (I : UU) (h : isaset I), I → list nat.

Definition BindingSigIndex : BindingSig -> UU := pr1.
Definition BindingSigIsaset (s : BindingSig) : isaset (BindingSigIndex s) :=
  pr1 (pr2 s).
Definition BindingSigMap (s : BindingSig) : BindingSigIndex s -> list nat :=
  pr2 (pr2 s).

Definition mkBindingSig {I : UU} (h : isaset I) (f : I -> list nat) : BindingSig := (I,,h,,f).

(** Sum of binding signatures *)
Definition SumBindingSig : BindingSig -> BindingSig -> BindingSig.
Proof.
intros s1 s2.
mkpair.
- apply (BindingSigIndex s1 ⨿ BindingSigIndex s2).
- mkpair.
  + apply (isasetcoprod _ _ (BindingSigIsaset s1) (BindingSigIsaset s2)).
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

Local Notation "'[C,C]'" := (functor_precategory C C hsC).

Local Definition has_homsets_C2 : has_homsets [C,C].
Proof.
apply functor_category_has_homsets.
Defined.

(** Form "_ o option^n" and return Id if n = 0 *)
Definition precomp_option_iter (BCC : BinCoproducts C) (TC : Terminal C) (n : nat) : functor [C,C] [C,C].
Proof.
induction n as [|n IHn].
- apply functor_identity.
- apply (pre_composition_functor _ _ _ hsC _ (iter_functor1 _ (option_functor BCC TC) n)).
Defined.

Lemma is_omega_cocont_precomp_option_iter
  (BCC : BinCoproducts C) (TC : Terminal C)
  (CLC : Colims_of_shape nat_graph C) (n : nat) :
  is_omega_cocont (precomp_option_iter BCC TC n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity has_homsets_C2).
- apply is_omega_cocont_pre_composition_functor, CLC.
Defined.

Definition precomp_option_iter_Signature (BCC : BinCoproducts C)
  (TC : Terminal C) (n : nat) : Signature C hsC C hsC.
Proof.
  mkpair.
  - exact (precomp_option_iter BCC TC n).
  - destruct n; simpl.
    + apply θ_functor_identity.
    + exact (pr2 (θ_from_δ_Signature C hsC _ (DL_iter_functor1 C hsC (option_functor BCC TC) (option_DistributiveLaw C hsC TC BCC) n))).
Defined.

(* will not be used, is just a confirmation of proper construction *)
Local Lemma functor_in_precomp_option_iter_Signature_ok  (BCC : BinCoproducts C)
      (TC : Terminal C) (n : nat) : Signature_Functor _ _ _ _ (precomp_option_iter_Signature BCC TC n) = precomp_option_iter BCC TC n.
Proof.
apply idpath.
Qed.


(* From here on all constructions need these hypotheses *)
Context (BPC : BinProducts C) (BCC : BinCoproducts C).

(** [nat] to a Signature *)
Definition Arity_to_Signature (TC : Terminal C) (xs : list nat) : Signature C hsC C hsC :=
     foldr1 (BinProduct_of_Signatures _ _ _ _ BPC) (IdSignature _ _)
        (map (precomp_option_iter_Signature BCC TC) xs).

Let BPC2 BPC := BinProducts_functor_precat C _ BPC hsC.
Let constprod_functor1 := constprod_functor1 (BPC2 BPC).

(** The H assumption follows directly if [C,C] has exponentials *)
Lemma is_omega_cocont_Arity_to_Signature
  (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
  (H : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (xs : list nat) :
  is_omega_cocont (Arity_to_Signature TC xs).
Proof.
destruct xs as [[|n] xs].
- destruct xs; apply (is_omega_cocont_functor_identity has_homsets_C2).
- induction n as [|n IHn].
  + destruct xs as [m []]; simpl.
    unfold Arity_to_Signature.
    apply is_omega_cocont_precomp_option_iter, CLC.
  + destruct xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_Signatures.
    * apply is_omega_cocont_precomp_option_iter, CLC.
    * apply (IHn (k,,xs)).
    * assumption.
    * intro x; apply (H x).
Defined.

(** ** Binding signature to a signature with strength *)
Definition BindingSigToSignature (TC : Terminal C)
  (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
  Signature C hsC C hsC.
Proof.
apply (Sum_of_Signatures (BindingSigIndex sig)).
- apply CC.
- intro i; apply (Arity_to_Signature TC (BindingSigMap sig i)).
Defined.

Lemma is_omega_cocont_BindingSigToSignature
  (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
  (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (sig : BindingSig)
  (CC : Coproducts (BindingSigIndex sig) C) (PC : Products (BindingSigIndex sig) C) :
  is_omega_cocont (BindingSigToSignature TC sig CC).
Proof.
apply is_omega_cocont_Sum_of_Signatures.
- intro i; apply is_omega_cocont_Arity_to_Signature, HF; assumption.
- apply PC.
Defined.

Let Id_H := Id_H C hsC BCC.
Let FunctorAlg F := FunctorAlg F has_homsets_C2.

(** ** Construction of initial algebra for a signature with strength *)
Definition SignatureInitialAlgebra
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Signature C hsC C hsC) (Hs : is_omega_cocont H) :
  Initial (FunctorAlg (Id_H H)).
Proof.
use colimAlgInitial.
- apply (Initial_functor_precat _ _ IC).
- apply (is_omega_cocont_Id_H _ _ _ _ Hs).
- apply ColimsFunctorCategory_of_shape, CLC.
Defined.

Let HSS := @hss_precategory C hsC BCC.

(* Redefine this here so that it uses the arguments above *)
Let InitialHSS
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Signature C hsC C hsC) (Hs : is_omega_cocont H) :
  Initial (HSS H).
Proof.
apply InitialHSS; assumption.
Defined.

(** ** Signature with strength and initial algebra to a HSS *)
Definition SignatureToHSS
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Signature C hsC C hsC) (Hs : is_omega_cocont H) :
  HSS H.
Proof.
now apply InitialHSS; assumption.
Defined.

(** The above HSS is initial *)
Definition SignatureToHSSisInitial
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Signature C hsC C hsC) (Hs : is_omega_cocont H) :
  isInitial _ (SignatureToHSS IC CLC H Hs).
Proof.
now unfold SignatureToHSS; destruct InitialHSS.
Qed.

(* Redefine this here so that it uses the arguments above *)
Let Monad_from_hss (H : Signature C hsC C hsC) : HSS H → Monad C.
Proof.
exact (Monad_from_hss _ _ BCC H).
Defined.

(** ** Function from binding signatures to monads *)
Definition BindingSigToMonad
  (TC : Terminal C) (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (sig : BindingSig)
  (PC : Products (BindingSigIndex sig) C)
  (CC : Coproducts (BindingSigIndex sig) C) :
  Monad C.
Proof.
use Monad_from_hss.
- apply (BindingSigToSignature TC sig CC).
- apply (SignatureToHSS IC CLC).
  apply (is_omega_cocont_BindingSigToSignature TC CLC HF _ _ PC).
Defined.

End BindingSigToMonad.

(** * Specialized versions of some of the above functions for HSET *)
Section BindingSigToMonadHSET.

Local Definition has_homsets_HSET2 : has_homsets [HSET,HSET,has_homsets_HSET].
Proof.
apply functor_category_has_homsets.
Defined.

(** ** Binding signature to signature with strength for HSET *)
Definition BindingSigToSignatureHSET (sig : BindingSig) : Signature HSET has_homsets_HSET HSET has_homsets_HSET.
Proof.
use BindingSigToSignature.
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply TerminalHSET.
- apply sig.
- apply CoproductsHSET, (BindingSigIsaset sig).
Defined.

Lemma is_omega_cocont_BindingSigToSignatureHSET (sig : BindingSig) :
  is_omega_cocont (BindingSigToSignatureHSET sig).
Proof.
apply is_omega_cocont_Sum_of_Signatures.
- intro i; apply is_omega_cocont_Arity_to_Signature.
  + apply ColimsHSET_of_shape.
  + intros F.
    apply (is_omega_cocont_constprod_functor1 _ has_homsets_HSET2).
    apply has_exponentials_functor_HSET, has_homsets_HSET.
- apply ProductsHSET.
Defined.

(** ** Construction of initial algebra for a signature with strength for HSET *)
Definition SignatureInitialAlgebraHSET (s : Signature HSET has_homsets_HSET _ _) (Hs : is_omega_cocont s) :
  Initial (FunctorAlg (Id_H _ _ BinCoproductsHSET s) has_homsets_HSET2).
Proof.
apply SignatureInitialAlgebra; try assumption.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
Defined.

(** ** Binding signature to a monad for HSET *)
Definition BindingSigToMonadHSET : BindingSig → Monad HSET.
Proof.
intros sig; use (BindingSigToMonad _ _ _ _ _ _ _ sig).
- apply has_homsets_HSET.
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply TerminalHSET.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- intros F.
  apply (is_omega_cocont_constprod_functor1 _ has_homsets_HSET2).
  apply has_exponentials_functor_HSET, has_homsets_HSET.
- apply ProductsHSET.
- apply CoproductsHSET.
  apply BindingSigIsaset.
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
