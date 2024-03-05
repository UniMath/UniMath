(**

This file constructs a substitution monad on Set from a binding signature for the syntax of
Martin-Löf type theory a la "Constructive Mathematics and Computer Programming" (1979).

Written by: Anders Mörtberg, 2016

version for simplified notion of HSS by Ralph Matthes (2022, 2023)
the file is identical to the homonymous file in the parent directory, except for importing files from the present directory

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.Notation.
Require UniMath.SubstitutionSystems.SubstitutionSystems.
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.LiftingInitial_alt.

Local Infix "::" := (@cons nat).
Local Notation "[]" := (@nil nat) (at level 0, format "[]").
Local Notation "'HSET2'":= [HSET, HSET].

Section preamble.

Definition four_rec {A : UU} (a b c d : A) : stn 4 -> A.
Proof.
induction 1 as [n p].
induction n as [|n _]; [apply a|].
induction n as [|n _]; [apply b|].
induction n as [|n _]; [apply c|].
induction n as [|n _]; [apply d|].
induction (nopathsfalsetotrue p).
Defined.

End preamble.

Infix "++" := SumBindingSig.

Section MLTT79.

(** This is the syntax as presented on page 158:
<<
Pi types           (∏x:A)B                     [0,1]
lambda             (λx)b                       [1]
application        (c)a                        [0,0]

Sigma types        (∑x:A)B                     [0,1]
pair               (a,b)                       [0,0]
pair-elim          (Ex,y)(c,d)                 [0,2]

Sum types          A + B                       [0,0]
inl                i(a)                        [0]
inr                j(b)                        [0]
sum-elim           (Dx,y)(c,d,e)               [0,1,1]

Id types           I(A,a,b)                    [0,0,0]
refl               r                           []
J                  J(c,d)                      [0,0]

Fin types          N_i                         []
Fin elems          0_i ... (i-1)_i             [] ... []    (i times)
Fin-elim           R_i(c,c_0,...,c_(i-1))      [0,0,...,0]  (i+1 zeroes)

Nat                N                           []
zero               0                           []
suc                a'                          [0]
nat-elim           (Rx,y)(c,d,e)               [0,0,2]

W-types            (Wx∈A)B                     [0,1]
sup                sup(a,b)                    [0,0]
W-elim             (Tx,y,z)(c,d)               [0,3]

Universes          U_0,U_1,...                 [],[],...
>>
*)

(** Some convenient notations *)
Local Notation "[0]" := (0 :: []).
Local Notation "[1]" := (1 :: []).
Local Notation "[0,0]" := (0 :: 0 :: []).
Local Notation "[0,1]" := (0 :: 1 :: []).
Local Notation "[0,2]" := (0 :: 2 :: []).
Local Notation "[0,3]" := (0 :: 3 :: []).
Local Notation "[0,0,0]" := (0 :: 0 :: 0 :: []).
Local Notation "[0,0,2]" := (0 :: 0 :: 2 :: []).
Local Notation "[0,1,1]" := (0 :: 1 :: 1 :: []).

Definition PiSig : BindingSig :=
  make_BindingSig (isasetstn 3) (three_rec [0,1] [1] [0,0]).

Definition SigmaSig : BindingSig :=
  make_BindingSig (isasetstn 3) (three_rec [0,1] [0,0] [0,2]).

Definition SumSig : BindingSig :=
  make_BindingSig (isasetstn 4) (four_rec [0,0] [0] [0] [0,1,1]).

Definition IdSig : BindingSig :=
  make_BindingSig (isasetstn 3) (three_rec [0,0,0] [] [0,0]).

(** Define the arity of the eliminators for Fin by recursion *)
Definition FinSigElim (n : nat) : list nat.
Proof.
induction n as [|n ih].
- apply [0].
- apply (0 :: ih).
Defined.

(** Define the signature of the constructors for Fin *)
Definition FinSigConstructors (n : nat) : stn n -> list nat := λ _, [].

(* The FinSig family is defined by recursion and decomposed into the
   type, the constructors and the eliminator *)
(* Definition FinSig (n : nat) : BindingSig (unit ⨿ (stn n ⨿ unit)). *)
(* Proof. *)
(* induction 1 as [_|p]. *)
(* - apply []. *)
(* - induction p as [p|]. *)
(*   + apply (FinSigConstructors _ p). *)
(*   + apply (FinSigElim n). *)
(* Defined. *)

(** Uncurried version of the FinSig family *)
Definition FinSigFun : (∑ n : nat, unit ⨿ (stn n ⨿ unit)) → list nat.
Proof.
induction 1 as [n p].
induction p as [_|p].
- apply [].
- induction p as [p|].
  + apply (FinSigConstructors _ p).
  + apply (FinSigElim n).
Defined.

Lemma isasetFinSig : isaset (∑ n, unit ⨿ (stn n ⨿ unit)).
Proof.
  apply isaset_total2.
  - apply isasetnat.
  - intros. repeat apply isasetcoprod; try apply isasetunit.
    apply isasetstn.
Qed.

Lemma isdeceqFinSig : isdeceq (∑ n, unit ⨿ (stn n ⨿ unit)).
Proof.
  apply isdeceq_total2.
  - apply isdeceqnat.
  - intros. repeat apply isdeceqcoprod; try apply isdecequnit.
    apply isdeceqstn.
Defined.

Definition FinSig : BindingSig := make_BindingSig isasetFinSig FinSigFun.

Definition NatSig : BindingSig :=
  make_BindingSig (isasetstn 4) (four_rec [] [] [0] [0,0,2]).

Definition WSig : BindingSig :=
  make_BindingSig (isasetstn 3) (three_rec [0,1] [0,0] [0,3]).

Definition USig : BindingSig := make_BindingSig isasetnat (λ _, []).

Let SigHSET := Signature HSET HSET HSET.

(** The binding signature of MLTT79 *)
Definition MLTT79Sig := PiSig ++ SigmaSig ++ SumSig ++ IdSig ++
                        FinSig ++ NatSig ++ WSig ++ USig.

(* Check MLTT79Sig. *)

Definition MLTT79Signature : SigHSET := BindingSigToSignatureHSET MLTT79Sig.

Let Id_H := SubstitutionSystems.Id_H _ BinCoproductsHSET.

Definition MLTT79Functor : functor HSET2 HSET2 := Id_H (Presignature_Signature MLTT79Signature).

Definition MLTT79Monad : Monad HSET := BindingSigToMonadHSET MLTT79Sig.

Lemma MLTT79Functor_Initial :
   Initial (FunctorAlg MLTT79Functor).
Proof.
apply SignatureInitialAlgebraHSET, is_omega_cocont_BindingSigToSignatureHSET.
Defined.

Definition MLTT79 : HSET2 :=
  alg_carrier _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_mor : HSET2⟦MLTT79Functor MLTT79,MLTT79⟧ :=
  alg_map _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_alg : algebra_ob MLTT79Functor :=
  InitialObject MLTT79Functor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,MLTT79⟧ :=
  SubstitutionSystems.η MLTT79_alg.

(* TODO: define the rest of the constructors and computation rules? *)

End MLTT79.
