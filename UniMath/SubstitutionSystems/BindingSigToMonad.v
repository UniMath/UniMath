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

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Local Notation "[ C , D ]" := (functor_category C D).
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

Definition make_BindingSig {I : UU} (h : isaset I) (f : I -> list nat) : BindingSig := (I,,h,,f).

(** Sum of binding signatures *)
Definition SumBindingSig : BindingSig -> BindingSig -> BindingSig.
Proof.
intros s1 s2.
use tpair.
- apply (BindingSigIndex s1 ⨿ BindingSigIndex s2).
- use tpair.
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

Context {C : category}.

Local Notation "'[C,C]'" := (functor_category C C).

(** Form "_ o option^n" and return Id if n = 0 *)
Definition precomp_option_iter (BCC : BinCoproducts C) (TC : Terminal C) (n : nat) : functor [C,C] [C,C].
Proof.
induction n as [|n IHn].
- apply functor_identity.
- apply (pre_composition_functor _ _ _  (iter_functor1 _ (option_functor BCC TC) n)).
Defined.

Lemma is_omega_cocont_precomp_option_iter
  (BCC : BinCoproducts C) (TC : Terminal C)
  (CLC : Colims_of_shape nat_graph C) (n : nat) :
  is_omega_cocont (precomp_option_iter BCC TC n).
Proof.
destruct n; simpl.
- apply is_omega_cocont_functor_identity.
- apply is_omega_cocont_pre_composition_functor, CLC.
Defined.

Definition precomp_option_iter_Signature (BCC : BinCoproducts C)
  (TC : Terminal C) (n : nat) : Signature C C C.
Proof.
  use tpair.
  - exact (precomp_option_iter BCC TC n).
  - destruct n; simpl.
    + apply θ_functor_identity.
    + exact (pr2 (θ_from_δ_Signature C _ (DL_iter_functor1 C (option_functor BCC TC) (option_DistributiveLaw C TC BCC) n))).
Defined.

(* will not be used, is just a confirmation of proper construction *)
Local Lemma functor_in_precomp_option_iter_Signature_ok  (BCC : BinCoproducts C)
      (TC : Terminal C) (n : nat) : Signature_Functor (precomp_option_iter_Signature BCC TC n) = precomp_option_iter BCC TC n.
Proof.
apply idpath.
Qed.


(* From here on all constructions need these hypotheses *)
Context (BPC : BinProducts C) (BCC : BinCoproducts C).

(** [nat] to a Signature *)
Definition Arity_to_Signature (TC : Terminal C) (xs : list nat) : Signature C C C :=
  foldr1_map (BinProduct_of_Signatures _ _ _ BPC)
         (ConstConstSignature C C C (TerminalObject TC))
         (precomp_option_iter_Signature BCC TC) xs.

Let BPC2 BPC := BinProducts_functor_precat C C BPC.
Let constprod_functor1 := constprod_functor1 (BPC2 BPC).

(** The H assumption follows directly if [C,C] has exponentials *)
Lemma is_omega_cocont_Arity_to_Signature
  (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
  (H : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (xs : list nat) :
  is_omega_cocont (Arity_to_Signature TC xs).
Proof.
  refine (foldr1_map_ind_nodep (BinProduct_of_Signatures _ _ _ BPC) _ _ is_omega_cocont _ _ _ xs).
  - apply is_omega_cocont_constant_functor.
  - intro n. apply is_omega_cocont_precomp_option_iter, CLC.
  - intros m sig Hyp.
    apply is_omega_cocont_BinProduct_of_Signatures.
    + apply is_omega_cocont_precomp_option_iter, CLC.
    + exact Hyp.
    + exact BPC.
    + exact H.
Defined.

(** ** Binding signature to a signature with strength *)
Definition BindingSigToSignature (TC : Terminal C)
  (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
  Signature C C C.
Proof.
  apply (Sum_of_Signatures (BindingSigIndex sig)).
  - apply CC.
  - intro i; apply (Arity_to_Signature TC (BindingSigMap sig i)).
Defined.

Lemma is_omega_cocont_BindingSigToSignature
  (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
  (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
  is_omega_cocont (BindingSigToSignature TC sig CC).
Proof.
  unfold BindingSigToSignature.
  apply is_omega_cocont_Sum_of_Signatures.
  now intro i; apply is_omega_cocont_Arity_to_Signature, HF.
Defined.

Let Id_H := Id_H C BCC.

(** ** Construction of initial algebra for a signature with strength *)
Definition SignatureInitialAlgebra
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Presignature C C C) (Hs : is_omega_cocont H) :
  Initial (FunctorAlg (Id_H H)).
Proof.
use colimAlgInitial.
- apply (Initial_functor_precat _ _ IC).
- apply (is_omega_cocont_Id_H _ _ _ Hs).
- apply ColimsFunctorCategory_of_shape, CLC.
Defined.

(** ** Construction of datatype specified by a binding signature *)
Definition DatatypeOfBindingSig
  (IC : Initial C) (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
  (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
  Initial (FunctorAlg (Id_H (Presignature_Signature(BindingSigToSignature TC sig CC)))).
Proof.
apply SignatureInitialAlgebra; trivial.
now apply is_omega_cocont_BindingSigToSignature.
Defined.

Let HSS := @hss_category C BCC.

(* Redefine this here so that it uses the arguments above *)
Let InitialHSS
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Presignature C C C) (Hs : is_omega_cocont H) :
  Initial (HSS H).
Proof.
apply InitialHSS; assumption.
Defined.

(** ** Signature with strength and initial algebra to a HSS *)
Definition SignatureToHSS
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Presignature C C C) (Hs : is_omega_cocont H) :
  HSS H.
Proof.
now apply InitialHSS; assumption.
Defined.

(** The above HSS is initial *)
Definition SignatureToHSSisInitial
  (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (H : Presignature C C C) (Hs : is_omega_cocont H) :
  isInitial _ (SignatureToHSS IC CLC H Hs).
Proof.
now unfold SignatureToHSS; destruct InitialHSS.
Qed.

(* Redefine this here so that it uses the arguments above *)
Let Monad_from_hss (H : Signature C C C) : HSS H → Monad C.
Proof.
exact (Monad_from_hss _ BCC H).
Defined.

(** ** Function from binding signatures to monads *)
Definition BindingSigToMonad
  (TC : Terminal C) (IC : Initial C) (CLC : Colims_of_shape nat_graph C)
  (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
  (sig : BindingSig)
  (CC : Coproducts (BindingSigIndex sig) C) :
  Monad C.
Proof.
use Monad_from_hss.
- apply (BindingSigToSignature TC sig CC).
- apply (SignatureToHSS IC CLC).
  apply (is_omega_cocont_BindingSigToSignature TC CLC HF _ _).
Defined.

End BindingSigToMonad.

(** * Specialized versions of some of the above functions for HSET *)
Section BindingSigToMonadHSET.

(** ** Binding signature to signature with strength for HSET *)
Definition BindingSigToSignatureHSET (sig : BindingSig) : Signature HSET HSET HSET.
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
intro i; apply is_omega_cocont_Arity_to_Signature.
+ apply ColimsHSET_of_shape.
+ intros F.
  apply is_omega_cocont_constprod_functor1.
  apply Exponentials_functor_HSET.
Defined.

(** ** Construction of initial algebra for a signature with strength for HSET *)
Definition SignatureInitialAlgebraHSET (s : Presignature HSET _ _) (Hs : is_omega_cocont s) :
  Initial (FunctorAlg (Id_H _ BinCoproductsHSET s)).
Proof.
apply SignatureInitialAlgebra; try assumption.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
Defined.

(** ** Binding signature to a monad for HSET *)
Definition BindingSigToMonadHSET : BindingSig → Monad HSET.
Proof.
intros sig; use (BindingSigToMonad _ _ _ _ _ _ sig).
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply TerminalHSET.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- intros F.
  apply is_omega_cocont_constprod_functor1.
  apply Exponentials_functor_HSET.
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
