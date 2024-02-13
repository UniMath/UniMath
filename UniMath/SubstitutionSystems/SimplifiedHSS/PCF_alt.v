(**

Syntax of PCF as a multisorted binding signature.

Written by: Anders Mörtberg, 2021

version for simplified notion of HSS by Ralph Matthes (2022, 2023)
the file is identical to the homonymous file in the parent directory, except for importing files from the present directory

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.STLC_alt.

Local Open Scope cat.

Section pcf.

(* Was there a general version of this somewhere? *)
Definition six_rec {A : UU} (i : stn 6) (a b c d e f : A) : A.
Proof.
induction i as [n p].
induction n as [|n _]; [apply a|].
induction n as [|n _]; [apply b|].
induction n as [|n _]; [apply c|].
induction n as [|n _]; [apply d|].
induction n as [|n _]; [apply e|].
induction n as [|n _]; [apply f|].
induction (nopathsfalsetotrue p).
Defined.

(** We assume a set of types with bool, nat and function types *)
Context (type : hSet) (Bool Nat : type) (arr : type → type → type).

Local Lemma htype : isofhlevel 3 type.
Proof.
exact (isofhlevelssnset 1 type (setproperty type)).
Defined.

Let typeToSet : category := [path_pregroupoid type htype,HSET].
Let typeToSet2 := [typeToSet,typeToSet].

Local Lemma BinCoprodTypeToSet : BinCoproducts typeToSet.
Proof.
apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Local Lemma TerminalTypeToSet : Terminal typeToSet.
Proof.
apply Terminal_functor_precat, TerminalHSET.
Defined.

Local Lemma BinProd : BinProducts [typeToSet,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Lemma BinCoprodTypeToSet2 : BinCoproducts typeToSet2.
Proof.
apply BinCoproducts_functor_precat, BinCoprodTypeToSet.
Defined.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).
Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodTypeToSet a b)).
Local Notation "'1'" := (TerminalObject TerminalTypeToSet).
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).
Infix "++" := (SumMultiSortedSig _).

(**

The Inductive version of PCF that we are going to model (copied from
https://github.com/benediktahrens/monads/blob/trunk/PCF/pcf.v):

<<
Inductive TY :=
 | Bool : TY
 | Nat : TY
 | arrow: TY -> TY -> TY.

Inductive PCF_consts : TY -> Type :=
 | Nats : nat -> PCF_consts Nat
 | tt : PCF_consts Bool
 | ff : PCF_consts Bool
 | succ : PCF_consts (arrow Nat Nat)
 | is_zero : PCF_consts (arr Nat Bool)
 | condN: PCF_consts (arrow Bool (arrow Nat (arrow Nat Nat)))
 | condB: PCF_consts (arrow Bool (arrow Bool (arrow Bool Bool))).

Inductive PCF (V:TY -> Type) : TY -> Type:=
 | PCFVar : forall t, V t -> PCF V t
 | Const  : forall t, PCF_consts t -> PCF V t
 | Bottom : forall t, PCF V t
 | PApp   : forall t s, PCF V (arrow s t) -> PCF V s -> PCF V t
 | PLam   : forall t s, PCF (opt_T t V) s -> PCF V (arrow t s)
 | PRec   : forall t, PCF V (arrow t t) -> PCF V t.
>>

We do this by defining the constants and non-constants separately and
then taking the sum of the signatures.

*)

Definition PCF_Consts : MultiSortedSig type.
Proof.
use make_MultiSortedSig.
- exact ((nat,,isasetnat) + (stn 6,,isasetstn 6))%set.
- induction 1 as [n|i].
  + exact ([],,Nat).                                   (* Nat (one for each nat) *)
  + apply (six_rec i).
    * exact ([],,Bool).                                (* True *)
    * exact ([],,Bool).                                (* False *)
    * exact ([],,arr Nat Nat).                         (* Succ *)
    * exact ([],,arr Nat Bool).                        (* is_zero *)
    * exact ([],,arr Bool (arr Nat (arr Nat Nat))).    (* CondN *)
    * exact ([],,arr Bool (arr Bool (arr Bool Bool))). (* CondB *)
Defined.

(* We could define PCF as follows, but we instead get App and Lam from the STLC signature *)
(* Definition PCF : MultiSortedSig type. *)
(* Proof. *)
(* use make_MultiSortedSig. *)
(* - apply (type + (type × type) + (type × type) + type)%set. *)
(* - intros [[[t|[t s]]|[t s]]|t]. *)
(*   * exact ([],,t).                                  (* Bottom *) *)
(*   * exact ((([],,(arr s t)) :: ([],,s) :: nil),,t). (* App *) *)
(*   * exact (((cons t [],,s) :: []),,(arr t s)).      (* Lam *) *)
(*   * exact ((([],,(arr t t)) :: nil),,t).            (* Y *) *)
(* Defined. *)

Definition PCF_Bot_Y : MultiSortedSig type.
Proof.
use make_MultiSortedSig.
- apply (type + type)%set.
- intros [t|t].
  * exact ([],,t).                                  (* Bottom *)
  * exact ((([],,(arr t t)) :: nil),,t).            (* Y *)
Defined.

Definition PCF_App_Lam : MultiSortedSig type := STLC_Sig type arr.

Definition PCF_Sig : MultiSortedSig type :=
  PCF_Consts ++ PCF_Bot_Y ++ PCF_App_Lam.

Definition PCF_Signature : Signature typeToSet _ _ :=
  MultiSortedSigToSignatureSet type htype PCF_Sig.

Definition PCF_Functor : functor typeToSet2 typeToSet2 :=
  Id_H _ BinCoprodTypeToSet PCF_Signature.

Lemma PCF_Functor_Initial : Initial (FunctorAlg PCF_Functor).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + apply ProductsHSET.
  + apply Exponentials_functor_HSET.
  + apply ColimsHSET_of_shape.
Defined.

Definition PCF_Monad : Monad typeToSet :=
  MultiSortedSigToMonadSet type htype PCF_Sig.

(** Extract the constructors from the initial algebra *)
Definition PCF_M : typeToSet2 :=
  alg_carrier _ (InitialObject PCF_Functor_Initial).

Let PCF_M_mor : typeToSet2⟦PCF_Functor PCF_M,PCF_M⟧ :=
  alg_map _ (InitialObject PCF_Functor_Initial).

Let PCF_M_alg : algebra_ob PCF_Functor :=
  InitialObject PCF_Functor_Initial.

(** The variables *)
Definition var_map : typeToSet2⟦Id,PCF_M⟧ :=
  BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · PCF_M_mor.

(* We can also extract the other constructors *)

End pcf.
