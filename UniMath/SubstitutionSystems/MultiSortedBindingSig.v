(**

the syntax of multi-sorted binding signatures, with examples

moved here in 2024 from other places in the package
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
(* Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids. *)

Require Import UniMath.SubstitutionSystems.BindingSigToMonad.


Local Open Scope cat.

Section MBindingSig.

(* Interestingly we later only need that [sort] is a 1-type *)
Context (sort : UU) (*(Hsort : isofhlevel 3 sort) *).

(** Definition of multisorted binding signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition make_MultiSortedSig {I : hSet}
  (ar : I → list (list sort × sort) × sort) : MultiSortedSig := (I,,ar).

(** Sum of multisorted binding signatures *)
Definition SumMultiSortedSig : MultiSortedSig → MultiSortedSig → MultiSortedSig.
Proof.
intros s1 s2.
use tpair.
- apply (setcoprod (ops s1) (ops s2)).
- induction 1 as [i|i].
  + apply (arity s1 i).
  + apply (arity s2 i).
Defined.

Section MultiSortedSigFromBindingSig.

  Context (s : BindingSig).

  Let I : hSet := BindingSigIndex s,, BindingSigIsaset s.

  Context (uni : sort). (** the unique sort being used *)

  (** create liste with [n] identical elements *)
  Definition n_list {A : UU} (n : nat) (a : A) : list A.
  Proof.
    induction n as [|n ].
    - exact nil.
    - exact (cons a IHn).
  Defined.

  Definition translateArity : nat -> list sort × sort.
  Proof.
    intro n.
    refine (_,, uni).
    exact (n_list n uni).
  Defined.

  Definition arFromBindingSig : I → list (list sort × sort) × sort.
  Proof.
    intro i.
    refine (_,, uni).
    set (nbbindersallargs := BindingSigMap s i).
    exact (map translateArity  nbbindersallargs).
  Defined.

  Definition MultiSortedSigFromBindingSig : MultiSortedSig
    := I ,, arFromBindingSig.

End MultiSortedSigFromBindingSig.

End MBindingSig.

(** Some notations *)
  Local Infix "::" := (@cons _).
  Local Notation "[]" := (@nil _) (at level 0, format "[]").
  Local Notation "a + b" := (setcoprod a b) : set.

Section STLC.
  (** the example of simply-typed lambda calculus *)

  Context (sort : hSet) (arr : sort → sort → sort).

  Local Notation "s ⇒ t" := (arr s t).

  Lemma STLC_Hsort : isofhlevel 3 sort.
  Proof.
    exact (isofhlevelssnset 1 sort (setproperty sort)).
  Defined.

  Definition STLC_Sig : MultiSortedSig sort.
  Proof.
    use make_MultiSortedSig.
    - apply ((sort × sort) + (sort × sort))%set.
    - intros H; induction H as [st|st]; induction st as [s t].
      + exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,t).
      + exact (((cons s [],,t) :: []),,(s ⇒ t)).
  Defined.

End STLC.

Section PCF.
  (** Written by: Anders Mörtberg, 2021 *)

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

Local Lemma PCF_Hsort : isofhlevel 3 type.
Proof.
exact (isofhlevelssnset 1 type (setproperty type)).
Defined.

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

End PCF.

Section CCS.
(**

Syntax of the calculus of constructions as in Streicher
"Semantics of Type Theory" formalized as a multisorted
binding signature.

Written by: Anders Mörtberg, 2017

 *)

(** We assume a two element set of sorts *)
  Definition CCSsort : hSet := @tpair _ (λ X, isaset X) bool isasetbool.

Lemma CCS_Hsort : isofhlevel 3 CCSsort.
Proof.
exact (isofhlevelssnset 1 CCSsort (setproperty CCSsort)).
Defined.

Definition CCSty : CCSsort := true.
Definition CCSel : CCSsort := false.

(** The grammar of expressions and objects from page 157:
<<
E ::= (Πx:E) E                product of types
    | Prop                    type of propositions
    | Proof(t)                type of proofs of proposition t

t ::= x                       variable
    | (λx:E) t                function abstraction
    | App([x:E] E, t, t)      function application
    | (∀x:E) t                universal quantification
>>

We refer to the first syntactic class as ty and the second as el. We first reformulate the rules as
follows:
<<
A,B ::= Π(A,x.B)              product of types
      | Prop                  type of propositions
      | Proof(t)              type of proofs of proposition t

t,u ::= x                     variable
      | λ(A,x.t)              function abstraction
      | App(A,x.B,t,u)        function application
      | ∀(A,x.t)              universal quantification
>>

This grammar then gives 6 operations, to the left as Vladimir's restricted 2-sorted signature (where
el is 0 and ty is 1) and to the right as a multisorted signature:

((0, 1), (1, 1), 1)                 = (([],ty), ([el], ty), ty)
(1)                                 = ([],ty)
((0, 0), 1)                         = (([], el), ty)
((0, 1), (1, 0), 0)                 = (([], ty), ([el], el), el)
((0, 1), (1, 1), (0, 0), (0, 0), 0) = (([], ty), ([el], ty), ([], el), ([], el), el)
((0, 1), (1, 0), 0)                 = (([], ty), ([el], el), el)

*)

(** The multisorted signature of CC-S *)
Definition CCS_Sig : MultiSortedSig CCSsort.
Proof.
use make_MultiSortedSig.
- exact (stn 6,,isasetstn 6).
- intro i. apply (six_rec i).
  + exact ((([],,CCSty) :: (cons CCSel [],,CCSty) :: nil),,CCSty).
  + exact ([],,CCSty).
  + exact ((([],,CCSel) :: nil),,CCSty).
  + exact ((([],,CCSty) :: (cons CCSel [],,CCSel) :: nil),,CCSel).
  + exact ((([],,CCSty) :: (cons CCSel [],,CCSty) :: ([],,CCSel) :: ([],,CCSel) :: nil),,CCSel).
  + exact ((([],,CCSty) :: (cons CCSel [],,CCSel) :: nil),,CCSel).
Defined.

End CCS.
