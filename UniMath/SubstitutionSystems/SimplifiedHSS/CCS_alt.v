(**

Syntax of the calculus of constructions as in Streicher
"Semantics of Type Theory" formalized as a 2-sorted
binding signature.

Written by: Anders Mörtberg, 2021 (adapted from CCS.v)

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
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted_alt.

Local Open Scope cat.

Section ccs.

Let sort := CCSsort.
Let ty := CCSty.
Let el := CCSel.

Let Hsort := CCS_Hsort.

Let sortToSet : category := SortIndexing.sortToSet sort Hsort.
Let sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Let sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.

Let projSortToSet : sort -> sortToSetSet := projSortToSet sort Hsort.
Let hat_functorSet : sort -> HSET ⟶ sortToSet := hat_functorSet sort Hsort.
Let sorted_option_functorSet : sort → sortToSet2 := sorted_option_functorSet sort Hsort.

Local Definition BCsortToSet : BinCoproducts sortToSet := SortIndexing.BCsortToSet sort Hsort.

Local Definition BPsortToSetSet : BinProducts sortToSetSet := SortIndexing.BPsortToSetSet sort Hsort.

  Local Notation "'Id'" := (functor_identity _).
  Local Notation "F ⊗ G" := (BinProduct_of_functors BPsortToSetSet F G).

Definition CCS_Signature : Signature sortToSet _ _ :=
  MultiSortedSigToSignatureSet sort Hsort CCS_Sig.

Definition CCS_Functor : functor sortToSet2 sortToSet2 :=
  Id_H _ BCsortToSet CCS_Signature.

Lemma CCS_Functor_Initial : Initial (FunctorAlg CCS_Functor).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + intros; apply ProductsHSET.
  + apply Exponentials_functor_HSET.
  + apply ColimsHSET_of_shape.
Defined.

Definition CCS_Monad : Monad sortToSet :=
  MultiSortedSigToMonadSet sort Hsort CCS_Sig.

(** Extract the constructors from the initial algebra *)
Definition CCS_M : sortToSet2 :=
  alg_carrier _ (InitialObject CCS_Functor_Initial).

Let CCS_M_mor : sortToSet2⟦CCS_Functor CCS_M,CCS_M⟧ :=
  alg_map _ (InitialObject CCS_Functor_Initial).

Let CCS_M_alg : algebra_ob CCS_Functor :=
  InitialObject CCS_Functor_Initial.

(** The variables *)
Definition var_map : sortToSet2⟦Id,CCS_M⟧ := η CCS_M_alg.

Definition Pi_source : functor sortToSet2 sortToSet2 :=
  ( post_comp_functor (projSortToSet ty) ⊗ ( pre_comp_functor (sorted_option_functorSet el)
                                                 ∙ post_comp_functor (projSortToSet ty)))
  ∙ (post_comp_functor (hat_functorSet ty)).

(** The Pi constructor *)
Definition Pi_map : sortToSet2⟦Pi_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 0)%stn)
  · τ CCS_M_alg.

Definition Prop_source : functor sortToSet2 sortToSet2.
Proof.
set (T := constant_functor [sortToSet,sortToSet] [sortToSet,HSET]
                           (constant_functor sortToSet HSET (TerminalObject TerminalHSET))).
exact (T ∙ post_comp_functor (hat_functorSet ty)).
Defined.

Definition Prop_map : sortToSet2⟦Prop_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 1%nat)%stn)
  · τ CCS_M_alg.

Definition Proof_source : functor sortToSet2 sortToSet2 :=
  post_comp_functor (projSortToSet el) ∙ post_comp_functor (hat_functorSet ty).

(** The Proof constructor *)
Definition Proof_map : sortToSet2⟦Proof_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 2)%stn)
  · τ CCS_M_alg.

Definition lam_source : functor sortToSet2 sortToSet2 :=
  (post_comp_functor (projSortToSet ty) ⊗ (pre_comp_functor (sorted_option_functorSet el)
   ∙ post_comp_functor (projSortToSet el)))
  ∙ (post_comp_functor (hat_functorSet el)).

(** The lambda constructor *)
Definition lam_map : sortToSet2⟦lam_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 3)%stn)
  · τ CCS_M_alg.

Definition app_source : functor sortToSet2 sortToSet2 :=
  ((post_comp_functor (projSortToSet ty)) ⊗
  ((pre_comp_functor (sorted_option_functorSet el) ∙ post_comp_functor (projSortToSet ty)) ⊗
  ((post_comp_functor (projSortToSet el)) ⊗
   (post_comp_functor (projSortToSet el)))))
 ∙ (post_comp_functor (hat_functorSet el)).

(** The app constructor *)
Definition app_map : sortToSet2⟦app_source CCS_M,CCS_M⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 4)%stn)
    · τ CCS_M_alg.

Definition forall_source : functor sortToSet2 sortToSet2 :=
  ((post_comp_functor (projSortToSet ty)) ⊗
   (pre_comp_functor (sorted_option_functorSet el) ∙ post_comp_functor (projSortToSet el)))
  ∙ post_comp_functor (hat_functorSet el).

(** The ∀ constructor *)
Definition forall_map : sortToSet2⟦forall_source CCS_M,CCS_M⟧ :=
    (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 5)%stn)
  · τ CCS_M_alg.

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
