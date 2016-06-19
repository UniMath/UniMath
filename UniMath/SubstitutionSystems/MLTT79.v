(**

Syntax of Martin-Löf type theory a la "Constructive Mathematics and
Computer Programming" (1979)

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

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
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.ArbitrarySumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.
Require Import UniMath.SubstitutionSystems.GenSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial.

Local Infix "::" := (cons_list nat).
Local Notation "[]" := (nil_list nat) (at level 0, format "[]").
Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Section preamble.

Definition three_rec {A : UU} (a b c : A) : stn 3 -> A.
Proof.
induction 1 as [n p].
induction n as [_|n _]; [apply a|].
induction n as [_|n _]; [apply b|].
induction n as [_|n _]; [apply c|].
induction (nopathsfalsetotrue p).
Defined.

Definition four_rec {A : UU} (a b c d : A) : stn 4 -> A.
Proof.
induction 1 as [n p].
induction n as [_|n _]; [apply a|].
induction n as [_|n _]; [apply b|].
induction n as [_|n _]; [apply c|].
induction n as [_|n _]; [apply d|].
induction (nopathsfalsetotrue p).
Defined.

Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

End preamble.

Infix "++" := SumGenSig.

Section MLTT79.

(** This is the syntax as presented on page 158:

Pi types           (Πx:A)B                     [0,1]
lambda             (λx)b                       [1]
application        (c)a                        [0,0]

Sigma types        (Σx:A)B                     [0,1]
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

*)

(* Some convenient notations *)
Local Notation "[0]" := (0 :: []).
Local Notation "[1]" := (1 :: []).
Local Notation "[0,0]" := (0 :: 0 :: []).
Local Notation "[0,1]" := (0 :: 1 :: []).
Local Notation "[0,2]" := (0 :: 2 :: []).
Local Notation "[0,3]" := (0 :: 3 :: []).
Local Notation "[0,0,0]" := (0 :: 0 :: 0 :: []).
Local Notation "[0,0,2]" := (0 :: 0 :: 2 :: []).
Local Notation "[0,1,1]" := (0 :: 1 :: 1 :: []).

Definition PiSig : GenSig :=
  mkGenSig (isdeceqstn 3) (three_rec [0,1] [1] [0,0]).

Definition SigmaSig : GenSig :=
  mkGenSig (isdeceqstn 3) (three_rec [0,1] [0,0] [0,2]).

Definition SumSig : GenSig :=
  mkGenSig (isdeceqstn 4) (four_rec [0,0] [0] [0] [0,1,1]).

Definition IdSig : GenSig :=
  mkGenSig (isdeceqstn 3) (three_rec [0,0,0] [] [0,0]).

(* Define the arity of the eliminators for Fin by recursion *)
Definition FinSigElim (n : nat) : list nat.
Proof.
induction n as [|n ih].
- apply [0].
- apply (0 :: ih).
Defined.

(* Define the signature of the constructors for Fin by recursion *)
Definition FinSigConstructors (n : nat) : stn n -> list nat := fun _ => [].

(* The FinSig family is defined by recursion and decomposed into the
   type, the constructors and the eliminator *)
(* Definition FinSig (n : nat) : GenSig (unit ⨿ (stn n ⨿ unit)). *)
(* Proof. *)
(* induction 1 as [_|p]. *)
(* - apply []. *)
(* - induction p as [p|]. *)
(*   + apply (FinSigConstructors _ p). *)
(*   + apply (FinSigElim n). *)
(* Defined. *)

(* Uncurried version of the FinSig family *)
Definition FinSigFun : (Σ n : nat, unit ⨿ (stn n ⨿ unit)) → list nat.
Proof.
induction 1 as [n p].
induction p as [_|p].
- apply [].
- induction p as [p|].
  + apply (FinSigConstructors _ p).
  + apply (FinSigElim n).
Defined.

Lemma isdeceqFinSig : isdeceq (Σ n, unit ⨿ (stn n ⨿ unit)).
Proof.
intros [n p] [m q].
induction (isdeceqnat n m) as [h|h].
- induction h.
   + destruct (isdeceqcoprod isdecequnit
                (isdeceqcoprod (isdeceqstn n) isdecequnit) p q) as [Hpq|Hpq].
     * now rewrite Hpq; apply inl.
     * apply inr; intro H.
       assert (Hid : maponpaths pr1 H = idpath _).
       { apply isasetnat. }
       generalize (fiber_paths H); unfold base_paths.
       rewrite Hid, idpath_transportf; intro H'.
       apply (Hpq H').
- apply inr; intro H; apply (h (maponpaths pr1 H)).
Defined.

Definition FinSig : GenSig := mkGenSig isdeceqFinSig FinSigFun.

Definition NatSig : GenSig :=
  mkGenSig (isdeceqstn 4) (four_rec [] [] [0] [0,0,2]).

Definition WSig : GenSig :=
  mkGenSig (isdeceqstn 3) (three_rec [0,1] [0,0] [0,3]).

Definition USig : GenSig := mkGenSig isdeceqnat (fun _ => []).

Let SigHSET := Signature HSET has_homsets_HSET.

Definition MLTT79Sig := PiSig ++ SigmaSig ++ SumSig ++ IdSig ++
                        FinSig ++ NatSig ++ WSig ++ USig.

(* Check MLTT79Sig. *)

Definition MLTT79Signature : SigHSET := GenSigToSignature MLTT79Sig.

Definition MLTT79Functor : functor HSET2 HSET2 :=
  Id_H _ _ CoproductsHSET MLTT79Signature.

Definition MLTT79Monad : Monad HSET := GenSigToMonad MLTT79Sig.

Lemma MLTT79Functor_Initial :
   Initial (FunctorAlg MLTT79Functor has_homsets_HSET2).
Proof.
apply (GenSigInitial MLTT79Sig).
Defined.

Definition MLTT79 : HSET2 :=
  alg_carrier _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_mor : HSET2⟦MLTT79Functor MLTT79,MLTT79⟧ :=
  alg_map _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_alg : algebra_ob MLTT79Functor :=
  InitialObject MLTT79Functor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,MLTT79⟧ :=
  CoproductIn1 HSET2 _ ;; MLTT79_mor.

(* TODO: define the rest of the constructors and computation rules? *)

End MLTT79.
