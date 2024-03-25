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

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Slice.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
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
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction.

Local Open Scope cat.

Section ccs.

Local Notation "C / X" := (slice_cat C X).

Let sort := CCSsort.
Let ty := CCSty.
Let el := CCSel.

Local Definition HSET_over_sort : category.
Proof.
exists (HSET / sort).
now apply has_homsets_slice_precat.
Defined.

Let HSET_over_sort2 := [HSET/sort,HSET_over_sort].

Definition CCS_Signature : Signature (HSET / sort) _ _ :=
  MultiSortedSigToSignature sort CCS_Sig.

Let Id_H := Id_H _ (BinCoproducts_HSET_slice sort).

Definition CCS_Functor : functor HSET_over_sort2 HSET_over_sort2 :=
  Id_H CCS_Signature.

Lemma CCS_Functor_Initial : Initial (FunctorAlg CCS_Functor).
Proof.
apply SignatureInitialAlgebraSetSort.
apply is_omega_cocont_MultiSortedSigToSignature.
apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

Definition CCS_Monad : Monad (HSET / sort) :=
  MultiSortedSigToMonad sort CCS_Sig.

(** Extract the constructors from the initial algebra *)
Definition CCS : HSET_over_sort2 :=
  alg_carrier _ (InitialObject CCS_Functor_Initial).

Let CCS_mor : HSET_over_sort2⟦CCS_Functor CCS,CCS⟧ :=
  alg_map _ (InitialObject CCS_Functor_Initial).

Let CCS_alg : algebra_ob CCS_Functor :=
  InitialObject CCS_Functor_Initial.


Local Lemma BP : BinProducts [HSET_over_sort,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'Id'" := (functor_identity HSET_over_sort).
Local Notation "x ⊗ y" := (BinProductObject _ (BP x y)).

(** The variables *)
Definition var_map : HSET_over_sort2⟦Id,CCS⟧ := η CCS_alg.

Definition Pi_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort ty)) ∙ hat_functor sort ty.

(** The Pi constructor *)
Definition Pi_map : HSET_over_sort2⟦Pi_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 0)%stn)
    ·  τ CCS_alg.

Definition Prop_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  constant_functor (slice_cat HSET _) HSET 1%CS  ∙ hat_functor sort ty.

Definition Prop_map : HSET_over_sort2⟦Prop_source CCS,CCS⟧.
Proof.
use ((CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 1)%stn)  · τ CCS_alg).
Defined.

Definition Proof_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  (X ∙ proj_functor sort el) ∙ hat_functor sort ty.

(** The Proof constructor *)
Definition Proof_map : HSET_over_sort2⟦Proof_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 2)%stn)
    · τ CCS_alg.

Definition lam_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort el)) ∙ hat_functor sort el.

(** The lambda constructor *)
Definition lam_map : HSET_over_sort2⟦lam_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 3)%stn)
    · τ CCS_alg.

Definition app_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗
  ((sorted_option_functor sort el ∙ X ∙ proj_functor sort ty) ⊗
  ((X ∙ proj_functor sort el) ⊗
   (X ∙ proj_functor sort el)))) ∙ hat_functor sort el.

(** The app constructor *)
Definition app_map : HSET_over_sort2⟦app_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 4)%stn)
    · τ CCS_alg.

Definition forall_source (X : HSET_over_sort2) : HSET_over_sort2 :=
  ((X ∙ proj_functor sort ty) ⊗ (sorted_option_functor sort el ∙ X ∙ proj_functor sort el)) ∙ hat_functor sort el.

(** The ∀ constructor *)
Definition forall_map : HSET_over_sort2⟦forall_source CCS,CCS⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (● 5)%stn)
    · τ CCS_alg.

Definition make_CCS_Algebra X
  (fvar    : HSET_over_sort2⟦Id,X⟧)
  (fPi     : HSET_over_sort2⟦Pi_source X,X⟧)
  (fProp   : HSET_over_sort2⟦Prop_source X,X⟧)
  (fProof  : HSET_over_sort2⟦Proof_source X,X⟧)
  (flam    : HSET_over_sort2⟦lam_source X,X⟧)
  (fapp    : HSET_over_sort2⟦app_source X,X⟧)
  (fforall : HSET_over_sort2⟦forall_source X,X⟧) : algebra_ob CCS_Functor.
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
Defined. (* This is slow *)

(** The recursor for ccs *)
Definition foldr_map X
  (fvar    : HSET_over_sort2⟦Id,X⟧)
  (fPi     : HSET_over_sort2⟦Pi_source X,X⟧)
  (fProp   : HSET_over_sort2⟦Prop_source X,X⟧)
  (fProof  : HSET_over_sort2⟦Proof_source X,X⟧)
  (flam    : HSET_over_sort2⟦lam_source X,X⟧)
  (fapp    : HSET_over_sort2⟦app_source X,X⟧)
  (fforall : HSET_over_sort2⟦forall_source X,X⟧) :
  algebra_mor _ CCS_alg (make_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall).
Proof.
apply (InitialArrow CCS_Functor_Initial (make_CCS_Algebra X fvar fPi fProp fProof flam fapp fforall)).
Defined.

End ccs.
