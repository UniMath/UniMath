(**

Syntax of the calculus of constructions as in Streicher
"Semantics of Type Theory" formalized as a 2-sorted
binding signature.

Written by: Anders Mörtberg, 2021 (adapted from CCS.v)

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
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted_alt.

Local Open Scope cat.

Section ccs.

(* Was there a general version of this somewhere? *)
Definition six_rec {A : UU} (a b c d e f : A) : stn 6 → A.
Proof.
induction 1 as [n p].
induction n as [|n _]; [apply a|].
induction n as [|n _]; [apply b|].
induction n as [|n _]; [apply c|].
induction n as [|n _]; [apply d|].
induction n as [|n _]; [apply e|].
induction n as [|n _]; [apply f|].
induction (nopathsfalsetotrue p).
Defined.

(** We assume a two element set of sorts *)
Definition sort : hSet := (bool,,isasetbool).

Local Lemma hsort : isofhlevel 3 sort.
Proof.
exact (isofhlevelssnset 1 sort (setproperty sort)).
Defined.

Definition ty : sort := true.
Definition el : sort := false.

Let sortToSet : category := [path_pregroupoid sort hsort,HSET].
Let sortToSet2 := [sortToSet,sortToSet].

Local Lemma BinCoprodSortToSet : BinCoproducts sortToSet.
Proof.
apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Local Lemma TerminalSortToSet : Terminal sortToSet.
Proof.
apply Terminal_functor_precat, TerminalHSET.
Defined.

Local Lemma BinProd : BinProducts [sortToSet,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).
Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)).
Local Notation "'1'" := (TerminalObject TerminalSortToSet).
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

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

We refer to the first syntactic class as ty and the second as el.
We first reformulate the rules as follows:
<<
A,B ::= Π(A,x.B)              product of types
      | Prop                  type of propositions
      | Proof(t)              type of proofs of proposition t

t,u ::= x                     variable
      | λ(A,x.t)              function abstraction
      | App(A,x.B,t,u)        function application
      | ∀(A,x.t)              universal quantification
>>

This grammar then gives 6 operations, to the left as Vladimir's restricted
2-sorted signature (where el is 0 and ty is 1) and to the right as a
 multisorted signature:

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

Definition CCS_Signature : Signature sortToSet _ _ :=
  MultiSortedSigToSignatureSet sort hsort CCS_Sig.

Definition CCS_Functor : functor sortToSet2 sortToSet2 :=
  Id_H _ BinCoprodSortToSet CCS_Signature.

Lemma CCS_Functor_Initial : Initial (FunctorAlg CCS_Functor).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + apply ProductsHSET.
  + apply Exponentials_functor_HSET.
  + apply ColimsHSET_of_shape.
Defined.

Definition CCS_Monad : Monad sortToSet :=
  MultiSortedSigToMonadSet sort hsort CCS_Sig.

(** Extract the constructors from the initial algebra *)
Definition CCS_M : sortToSet2 :=
  alg_carrier _ (InitialObject CCS_Functor_Initial).

Let CCS_M_mor : sortToSet2⟦CCS_Functor CCS_M,CCS_M⟧ :=
  alg_map _ (InitialObject CCS_Functor_Initial).

Let CCS_M_alg : algebra_ob CCS_Functor :=
  InitialObject CCS_Functor_Initial.

(** The variables *)
Definition var_map : sortToSet2⟦Id,CCS_M⟧ :=
  BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · CCS_M_mor.

Definition Pi_source : functor sortToSet2 sortToSet2 :=
  ( post_comp_functor (projSortToSet sort hsort ty) ⊗ ( pre_comp_functor (sorted_option_functorSet sort hsort el)
                                                 ∙ post_comp_functor (projSortToC sort hsort _ ty)))
  ∙ (post_comp_functor (hat_functorSet sort hsort ty)).

(** The Pi constructor *)
Definition Pi_map : sortToSet2⟦Pi_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 0)%stn)
  · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
  · CCS_M_mor.

Definition Prop_source : functor sortToSet2 sortToSet2.
Proof.
set (T := constant_functor [sortToSet,sortToSet] [sortToSet,HSET]
                           (constant_functor sortToSet HSET (TerminalObject TerminalHSET))).
exact (T ∙ post_comp_functor (hat_functorSet sort hsort ty)).
Defined.

Definition Prop_map : sortToSet2⟦Prop_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 1%nat)%stn)
  · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
  · CCS_M_mor.

Definition Proof_source : functor sortToSet2 sortToSet2 :=
  post_comp_functor (projSortToSet sort hsort el) ∙ post_comp_functor (hat_functorSet sort hsort ty).

(** The Proof constructor *)
Definition Proof_map : sortToSet2⟦Proof_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 2)%stn)
  · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
  · CCS_M_mor.

Definition lam_source : functor sortToSet2 sortToSet2 :=
  (post_comp_functor (projSortToSet sort hsort ty) ⊗ (pre_comp_functor (sorted_option_functorSet sort hsort el)
   ∙ post_comp_functor (projSortToC sort hsort _ el)))
  ∙ (post_comp_functor (hat_functorSet sort hsort el)).

(** The lambda constructor *)
Definition lam_map : sortToSet2⟦lam_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 3)%stn)
  · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
  · CCS_M_mor.

Definition app_source : functor sortToSet2 sortToSet2 :=
  ((post_comp_functor (projSortToSet sort hsort ty)) ⊗
  ((pre_comp_functor (sorted_option_functorSet sort hsort el) ∙ post_comp_functor (projSortToSet sort hsort ty)) ⊗
  ((post_comp_functor (projSortToSet sort hsort el)) ⊗
   (post_comp_functor (projSortToSet sort hsort el)))))
 ∙ (post_comp_functor (hat_functorSet sort hsort el)).

(** The app constructor *)
Definition app_map : sortToSet2⟦app_source CCS_M,CCS_M⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 4)%stn)
    · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
    · CCS_M_mor.

Definition forall_source : functor sortToSet2 sortToSet2 :=
  ((post_comp_functor (projSortToSet sort hsort ty)) ⊗
   (pre_comp_functor (sorted_option_functorSet sort hsort el) ∙ post_comp_functor (projSortToSet sort hsort el)))
  ∙ post_comp_functor (hat_functorSet sort hsort el).

(** The ∀ constructor *)
Definition forall_map : sortToSet2⟦forall_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 5)%stn)
  · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
  · CCS_M_mor.

Definition make_CCS_Algebra X
  (fvar    : sortToSet2⟦Id,X⟧)
  (fPi     : sortToSet2⟦Pi_source X,X⟧)
  (fProp   : sortToSet2⟦Prop_source X,X⟧)
  (fProof  : sortToSet2⟦Proof_source X,X⟧)
  (flam    : sortToSet2⟦lam_source X,X⟧)
  (fapp    : sortToSet2⟦app_source X,X⟧)
  (fforall : sortToSet2⟦forall_source X,X⟧) : algebra_ob CCS_Functor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ fvar).
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
Defined.

(** The recursor for ccs *)
Definition foldr_map X
  (fvar    : sortToSet2⟦Id,X⟧)
  (fPi     : sortToSet2⟦Pi_source X,X⟧)
  (fProp   : sortToSet2⟦Prop_source X,X⟧)
  (fProof  : sortToSet2⟦Proof_source X,X⟧)
  (flam    : sortToSet2⟦lam_source X,X⟧)
  (fapp    : sortToSet2⟦app_source X,X⟧)
  (fforall : sortToSet2⟦forall_source X,X⟧) :
  algebra_mor _ CCS_M_alg (make_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall).
Proof.
apply (InitialArrow CCS_Functor_Initial (make_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall)).
Defined.

End ccs.
