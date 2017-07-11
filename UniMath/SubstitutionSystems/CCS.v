(**

Syntax of the calculus of constructions as in Streicher
"Semantics of Type Theory" formalized as a multisorted
binding signature.

Written by: Anders Mörtberg, 2017

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted.
Require Import UniMath.SubstitutionSystems.MultiSorted.

Local Open Scope cat.

Section ccs.

(* Preliminary stuff, upstream? *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "C / X" := (slice_precat C X (homset_property C)).
Local Notation "a + b" := (setcoprod a b) : set.

(* Was there a general version of this somewhere? *)
Definition six_rec {A : UU} (a b c d e f : A) : stn 6 -> A.
Proof.
induction 1 as [n p].
induction n as [_|n _]; [apply a|].
induction n as [_|n _]; [apply b|].
induction n as [_|n _]; [apply c|].
induction n as [_|n _]; [apply d|].
induction n as [_|n _]; [apply e|].
induction n as [_|n _]; [apply f|].
induction (nopathsfalsetotrue p).
Defined.

(** We assume a two element set of sorts *)
Definition sort : hSet := @tpair _ (λ X, isaset X) bool isasetbool.

Definition ty : sort := true.
Definition el : sort := false.

Local Definition SET_over_sort : category.
Proof.
exists (SET / sort).
now apply has_homsets_slice_precat.
Defined.

Let hs : has_homsets (SET / sort) := homset_property SET_over_sort.
Let SET_over_sort2 := [SET/sort,SET_over_sort].

Local Lemma hs2 : has_homsets SET_over_sort2.
Proof.
apply functor_category_has_homsets.
Qed.


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
Definition CCS_Sig : MultiSortedSig sort.
Proof.
use mkMultiSortedSig.
- exact (stn 6,,isasetstn 6).
- apply six_rec.
  + exact ((([],,ty) :: (cons el [],,ty) :: nil),,ty).
  + exact ([],,ty).
  + exact ((([],,el) :: nil),,ty).
  + exact ((([],,ty) :: (cons el [],,el) :: nil),,el).
  + exact ((([],,ty) :: (cons el [],,ty) :: ([],,el) :: ([],,el) :: nil),,el).
  + exact ((([],,ty) :: (cons el [],,el) :: nil),,el).
Defined.

Definition CCS_Signature : Signature (SET / sort) _ _ _ :=
  MultiSortedSigToSignature sort CCS_Sig.

Let Id_H := Id_H _ hs (BinCoproducts_HSET_slice sort).

Definition CCS_Functor : functor SET_over_sort2 SET_over_sort2 :=
  Id_H CCS_Signature.

Lemma CCS_Functor_Initial : Initial (FunctorAlg CCS_Functor hs2).
Proof.
apply SignatureInitialAlgebraSetSort.
apply is_omega_cocont_MultiSortedSigToSignature.
apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

Definition CCS_Monad : Monad (SET / sort) :=
  MultiSortedSigToMonad sort CCS_Sig.

(** Extract the constructors from the initial algebra *)
Definition CCS : SET_over_sort2 :=
  alg_carrier _ (InitialObject CCS_Functor_Initial).

Let CCS_mor : SET_over_sort2⟦CCS_Functor CCS,CCS⟧ :=
  alg_map _ (InitialObject CCS_Functor_Initial).

Let CCS_alg : algebra_ob CCS_Functor :=
  InitialObject CCS_Functor_Initial.


Local Lemma BP : BinProducts [SET_over_sort,SET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'Id'" := (functor_identity SET_over_sort).
Local Notation "x ⊗ y" := (BinProductObject _ (BP x y)) (at level 10).

(** The variables *)
Definition var_map : SET_over_sort2⟦Id,CCS⟧ :=
  BinCoproductIn1 _ (BinCoproducts_functor_precat _ _ _ _ _ _) · CCS_mor.

Definition Pi_source (X : SET_over_sort2) : SET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort ty)) ∙ hat_functor sort ty.

(** The Pi constructor *)
Definition Pi_map : SET_over_sort2⟦Pi_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 0)%stn)
    · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _))
    · CCS_mor.

Definition Prop_source (X : SET_over_sort2) : SET_over_sort2 :=
  constant_functor (slice_precat HSET sort has_homsets_HSET) HSET 1%CS  ∙ hat_functor sort ty.

Definition Prop_map : SET_over_sort2⟦Prop_source CCS,CCS⟧.
Proof.
use ((CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 1)%stn) · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _)) · CCS_mor).
Defined.

Definition Proof_source (X : SET_over_sort2) : SET_over_sort2 :=
  (X ∙ proj_functor sort el) ∙ hat_functor sort ty.

(** The Proof constructor *)
Definition Proof_map : SET_over_sort2⟦Proof_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 2)%stn)
    · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _))
    · CCS_mor.

Definition lam_source (X : SET_over_sort2) : SET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort el)) ∙ hat_functor sort el.

(** The lambda constructor *)
Definition lam_map : SET_over_sort2⟦lam_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 3)%stn)
    · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _))
    · CCS_mor.

Definition app_source (X : SET_over_sort2) : SET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗
  ((sorted_option_functor sort el ∙ X ∙ proj_functor sort ty) ⊗
  ((X ∙ proj_functor sort el) ⊗
   (X ∙ proj_functor sort el)))) ∙ hat_functor sort el.

(** The app constructor *)
Definition app_map : SET_over_sort2⟦app_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 4)%stn)
    · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _))
    · CCS_mor.

Definition forall_source (X : SET_over_sort2) : SET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort el)) ∙ hat_functor sort el.

(** The ∀ constructor *)
Definition forall_map : SET_over_sort2⟦forall_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) (● 5)%stn)
    · (BinCoproductIn2 _ (BinCoproducts_functor_precat _ _ _ _ _ _))
    · CCS_mor.

Definition mk_CCS_Algebra X
  (fvar    : SET_over_sort2⟦Id,X⟧)
  (fPi     : SET_over_sort2⟦Pi_source X,X⟧)
  (fProp   : SET_over_sort2⟦Prop_source X,X⟧)
  (fProof  : SET_over_sort2⟦Proof_source X,X⟧)
  (flam    : SET_over_sort2⟦lam_source X,X⟧)
  (fapp    : SET_over_sort2⟦app_source X,X⟧)
  (fforall : SET_over_sort2⟦forall_source X,X⟧) : algebra_ob CCS_Functor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ _ fvar).
use CoproductArrow.
intros i.
induction i as [n p].
repeat (induction n as [|n _]; try induction (nopathsfalsetotrue p)).
- exact fPi.
- exact fProp.
- exact fProof.
- exact flam.
- simpl in fapp.
  exact fapp.
- exact fforall.
Defined. (* This is slow *)

(** The recursor for ccs *)
Definition foldr_map X
  (fvar    : SET_over_sort2⟦Id,X⟧)
  (fPi     : SET_over_sort2⟦Pi_source X,X⟧)
  (fProp   : SET_over_sort2⟦Prop_source X,X⟧)
  (fProof  : SET_over_sort2⟦Proof_source X,X⟧)
  (flam    : SET_over_sort2⟦lam_source X,X⟧)
  (fapp    : SET_over_sort2⟦app_source X,X⟧)
  (fforall : SET_over_sort2⟦forall_source X,X⟧) :
  algebra_mor _ CCS_alg (mk_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall).
Proof.
apply (InitialArrow CCS_Functor_Initial (mk_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall)).
Defined.

End ccs.
