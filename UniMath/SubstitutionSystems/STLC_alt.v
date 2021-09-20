(**

Syntax of the simply typed lambda calculus as a
multisorted signature.

Written by: Anders Mörtberg, 2021 (adapted from STLC.v)

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

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

Local Open Scope cat.

(** * The simply typed lambda calculus from a multisorted binding signature *)
Section Lam.

Variable (sort : hSet) (arr : sort → sort → sort).

Local Lemma hsort : isofhlevel 3 sort.
Proof.
exact (isofhlevelssnset 1 sort (setproperty sort)).
Defined.

(** A lot of notations, upstream? *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.

Let sortToSet : category := [path_pregroupoid sort,SET].
Let hs : has_homsets sortToSet := homset_property sortToSet.

Local Lemma BinCoprodSortToSet : BinCoproducts sortToSet.
Proof.
apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Local Lemma BinProd : BinProducts [sortToSet,SET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'1'" := (functor_identity _).

Let sortToSet2 := [sortToSet,sortToSet].
Let hs2 : has_homsets sortToSet2 := homset_property sortToSet2.

Local Lemma BinCoprodSortToSet2 : BinCoproducts sortToSet2.
Proof.
apply BinCoproducts_functor_precat, BinCoprodSortToSet.
Defined.

(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use mkMultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set.
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,arr s t) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,arr s t).
Defined.

(** The signature with strength for the simply typed lambda calculus *)
Definition STLC_Signature : Signature sortToSet hs _ hs _ hs :=
  MultiSortedSigToSignatureSet _ STLC_Sig.

Definition STLC_Functor : functor sortToSet2 sortToSet2 :=
  Id_H _ _ BinCoprodSortToSet STLC_Signature.

Lemma STLC_Functor_Initial : Initial (FunctorAlg STLC_Functor hs2).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + apply ProductsHSET.
  + apply Exponentials_functor_HSET, functor_category_has_homsets.
  + apply ColimsHSET_of_shape.
Defined.

Definition STLC_Monad : Monad sortToSet :=
  MultiSortedSigToMonadSet sort STLC_Sig.

(** Extract the constructors of the STLC from the initial algebra *)
Definition STLC : sortToSet2 :=
  alg_carrier _ (InitialObject STLC_Functor_Initial).

Let STLC_mor : sortToSet2⟦STLC_Functor STLC,STLC⟧ :=
  alg_map _ (InitialObject STLC_Functor_Initial).

Let STLC_alg : algebra_ob STLC_Functor :=
  InitialObject STLC_Functor_Initial.

(** The variables *)
Definition var_map : sortToSet2⟦1,STLC⟧ :=
  BinCoproductIn1 _ (BinCoprodSortToSet2 _ _) · STLC_mor.

Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

(** The source of the application constructor *)
Definition app_source (s t : sort) : functor sortToSet2 sortToSet2 :=
    (post_comp_functor (projSortToSet sort (arr s t)) ⊗ post_comp_functor (projSortToSet sort s))
  ∙ (post_comp_functor (hat_functorSet sort t)).

(** The application constructor *)
Definition app_map (s t : sort) : sortToSet2⟦app_source s t STLC,STLC⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ (λ _, _)) (ii1 (s,,t))
  · BinCoproductIn2 _ (BinCoprodSortToSet2 _ _)
  · STLC_mor.

(** The source of the lambda constructor *)
Definition lam_source (s t : sort) : functor sortToSet2 sortToSet2 :=
    pre_comp_functor (sorted_option_functorSet sort s)
  ∙ post_comp_functor (projSortToC sort _ t)
  ∙ post_comp_functor (hat_functorSet sort (arr s t)).

Definition lam_map (s t : sort) : sortToSet2⟦lam_source s t STLC,STLC⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ (λ _, _)) (ii2 (s,,t))
  · BinCoproductIn2 _ (BinCoprodSortToSet2 _ _)
  · STLC_mor.

Definition make_STLC_Algebra X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
    algebra_ob STLC_Functor.
Proof.
apply (tpair _ X), (BinCoproductArrow _ _ fvar), CoproductArrow; intros b.
induction b as [st|st]; induction st as [s t].
- exact (fapp s t).
- exact (flam s t).
Defined.

(** The recursor for the stlc *)
Definition foldr_map X (fvar : sortToSet2⟦1,X⟧)
                       (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
                       (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
                        algebra_mor _ STLC_alg (make_STLC_Algebra X fvar fapp flam) :=
  InitialArrow STLC_Functor_Initial (make_STLC_Algebra X fvar fapp flam).

(** The equation for variables *)
Lemma foldr_var X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
unfold var_map.
rewrite <- assoc, (algebra_mor_commutes _ _ _ (foldr_map _ _ _ _)), assoc.
etrans; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite id_left.
apply BinCoproductIn1Commutes.
Qed.

Lemma foldr_app X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  app_map s t · foldr_map X fvar fapp flam =
  # (pr1 (app_source s t)) (foldr_map X fvar fapp flam) · fapp s t.
Proof.
unfold app_map.
rewrite <- assoc.
etrans; [apply maponpaths, (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))|].
rewrite assoc.
etrans; [eapply cancel_postcomposition; rewrite <- assoc;
         apply maponpaths, BinCoproductOfArrowsIn2|].
rewrite <- !assoc.
etrans; [apply maponpaths, maponpaths, BinCoproductIn2Commutes|].
rewrite assoc.
etrans; [apply cancel_postcomposition; use (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ _ _ (λ _, _)))|].
rewrite <- assoc.
apply maponpaths.
exact (CoproductInCommutes _ _ _ _ _ _ (inl (s,,t))).
Qed.

Lemma foldr_lam X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  lam_map s t · foldr_map X fvar fapp flam =
  # (pr1 (lam_source s t)) (foldr_map X fvar fapp flam) · flam s t.
Proof.
unfold lam_map.
rewrite <- assoc.
etrans; [apply maponpaths, (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))|].
rewrite assoc.
etrans; [eapply cancel_postcomposition; rewrite <- assoc;
         apply maponpaths, BinCoproductOfArrowsIn2|].
rewrite <- !assoc.
etrans; [apply maponpaths, maponpaths, BinCoproductIn2Commutes|].
rewrite assoc.
etrans; [apply cancel_postcomposition; use (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ _ _ (λ _, _)))|].
rewrite <- assoc.
apply maponpaths.
exact (CoproductInCommutes _ _ _ _ _ _ (inr (s,,t))).
Qed.

End Lam.
