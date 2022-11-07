(**

Syntax of the simply typed lambda calculus as a multisorted signature.

Written by: Anders Mörtberg, 2017

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Slice.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
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
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted.
Require Import UniMath.SubstitutionSystems.MultiSorted.

Local Open Scope cat.

(** * The simply typed lambda calculus from a multisorted binding signature *)
Section Lam.

Variable (sort : hSet) (arr : sort → sort → sort).

(** A lot of notations, upstream? *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "C / X" := (slice_cat C X).
Local Notation "a + b" := (setcoprod a b) : set.

Local Definition HSET_over_sort : category.
Proof.
exists (HSET / sort).
now apply has_homsets_slice_precat.
Defined.

Let HSET_over_sort2 := [HSET/sort,HSET_over_sort].

Local Lemma BinProducts_HSET_over_sort2 : BinProducts HSET_over_sort2.
Proof.
apply BinProducts_functor_precat, BinProducts_slice_precat, PullbacksHSET.
Defined.

Local Lemma Coproducts_HSET_over_sort2 : Coproducts ((sort × sort) + (sort × sort))%set HSET_over_sort2.
Proof.
apply Coproducts_functor_precat, Coproducts_slice_precat, CoproductsHSET.
apply setproperty.
Defined.


(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set. (* todo: fix this once level of × is fixed *)
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,arr s t) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,arr s t).
Defined.

(** The signature with strength for the simply typed lambda calculus *)
Definition STLC_Signature : Signature (HSET / sort) _ _:=
  MultiSortedSigToSignature sort STLC_Sig.

Let Id_H := Id_H _ (BinCoproducts_HSET_slice sort).

Definition STLC_Functor : functor HSET_over_sort2 HSET_over_sort2 :=
  Id_H STLC_Signature.

Lemma STLC_Functor_Initial : Initial (FunctorAlg STLC_Functor).
Proof.
apply SignatureInitialAlgebraSetSort.
apply is_omega_cocont_MultiSortedSigToSignature.
apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

Definition STLC_Monad : Monad (HSET / sort) :=
  MultiSortedSigToMonad sort STLC_Sig.

(** Extract the constructors of the stlc from the initial algebra *)
Definition STLC : HSET_over_sort2 :=
  alg_carrier _ (InitialObject STLC_Functor_Initial).

Let STLC_mor : HSET_over_sort2⟦STLC_Functor STLC,STLC⟧ :=
  alg_map _ (InitialObject STLC_Functor_Initial).

Let STLC_alg : algebra_ob STLC_Functor :=
  InitialObject STLC_Functor_Initial.


Local Lemma BP : BinProducts [HSET_over_sort,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'1'" := (functor_identity HSET_over_sort).
Local Notation "x ⊗ y" := (BinProductObject _ (BP x y)).

(** The variables *)


Definition var_map : HSET_over_sort2⟦1,STLC⟧ :=
  BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · STLC_mor.

(** The source of the application constructor *)
Definition app_source (s t : sort) (X : HSET_over_sort2) : HSET_over_sort2 :=
  ((X ∙ proj_functor sort (arr s t)) ⊗ (X ∙ proj_functor sort s)) ∙ hat_functor sort t.

(** The application constructor *)
Definition app_map (s t : sort) : HSET_over_sort2⟦app_source s t STLC,STLC⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (ii1 (s,, t)))
    · (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _))
    · STLC_mor.

(** The source of the lambda constructor *)
Definition lam_source (s t : sort) (X : HSET_over_sort2) : HSET_over_sort2 :=
  (sorted_option_functor sort s ∙ X ∙ proj_functor sort t) ∙ hat_functor sort (arr s t).

Definition lam_map (s t : sort) : HSET_over_sort2⟦lam_source s t STLC,STLC⟧ :=
  (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) (ii2 (s,,t)))
    · BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _)
    · STLC_mor.

Definition make_STLC_Algebra X (fvar : HSET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, HSET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, HSET_over_sort2⟦lam_source s t X,X⟧) :
    algebra_ob STLC_Functor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ fvar).
use CoproductArrow.
intro b; induction b as [st|st]; induction st as [s t].
- apply (fapp s t).
- apply (flam s t).
Defined.

(** The recursor for the stlc *)
Definition foldr_map X (fvar : HSET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, HSET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, HSET_over_sort2⟦lam_source s t X,X⟧) :
  algebra_mor _ STLC_alg (make_STLC_Algebra X fvar fapp flam).
Proof.
apply (InitialArrow STLC_Functor_Initial (make_STLC_Algebra X fvar fapp flam)).
Defined.

(** The equation for variables *)
Lemma foldr_var X (fvar : HSET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, HSET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, HSET_over_sort2⟦lam_source s t X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
apply id_left.
Defined.

(* TODO: how to define the equations for app and lam? *)

End Lam.
