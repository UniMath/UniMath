(**

Syntax of the simply typed lambda calculus as a multisorted signature.

Written by: Anders Mörtberg, 2017

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

(** A lot of notations, upstream? *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.

Let sortToSet : category := [path_pregroupoid sort,SET].

Let hsSortToSet : has_homsets sortToSet := homset_property sortToSet.

Let sortToSet2 := [sortToSet,sortToSet].

Local Lemma hs2 : has_homsets sortToSet2.
Proof.
apply functor_category_has_homsets.
Qed.

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
Definition STLC_Signature : Signature _ hsSortToSet _ hsSortToSet _ hsSortToSet.
Proof.
use MultiSortedSigToSignature.
- apply isofhlevelssnset, setproperty.
- apply TerminalHSET.
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply CoproductsHSET.
- exact STLC_Sig.
Defined.

Lemma CSortToSet : BinCoproducts sortToSet.
Proof.
  apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Lemma CSortToSet2 : BinCoproducts sortToSet2.
Proof.
  apply BinCoproducts_functor_precat, BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Definition STLC_Functor : functor [sortToSet,sortToSet] [sortToSet,sortToSet].
Proof.
exact (Id_H _ _ CSortToSet STLC_Signature).
Defined.

Lemma STLC_Functor_Initial : Initial (FunctorAlg STLC_Functor hs2).
Proof.
apply SignatureInitialAlgebraSetSort.
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
Definition STLC : sortToSet2 := alg_carrier _ (InitialObject STLC_Functor_Initial).

Let STLC_mor : sortToSet2⟦STLC_Functor STLC,STLC⟧ :=
  alg_map _ (InitialObject STLC_Functor_Initial).

Let STLC_alg : algebra_ob STLC_Functor := InitialObject STLC_Functor_Initial.


Local Lemma BP : BinProducts [sortToSet,SET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'1'" := (functor_identity sortToSet).
Local Notation "x ⊗ y" := (BinProductObject _ (BP x y)).

(** The variables *)
Definition var_map : sortToSet2⟦1,STLC⟧.
Proof.
exact (BinCoproductIn1 _ (CSortToSet2 _ _) · STLC_mor).
Defined.
  (* BinCoproductIn1 _ (BinCoproducts_functor_precat _ _ _ _ _ _) · STLC_mor. *)

Definition hat_functor' : sort → SET ⟶ sortToSet.
Proof.
use hat_functor.
- apply isofhlevelssnset, setproperty.
- apply CoproductsHSET.
Defined.

Definition sorted_option_functor' : sort → sortToSet ⟶ sortToSet.
Proof.
use sorted_option_functor.
- apply isofhlevelssnset, setproperty.
- apply TerminalHSET.
- apply BinCoproductsHSET.
- apply CoproductsHSET.
Defined.

(** The source of the application constructor *)
Definition app_source (s t : sort) : functor sortToSet2 sortToSet2.
Proof.
  set (F := (BinProduct_of_functors BP (post_composition_functor (homset_property _) (homset_property _) (projSortToC sort _ (arr s t))) (post_composition_functor (homset_property _) _ (projSortToC sort _ s)))).
  apply (F ∙ post_composition_functor _ (homset_property _) (hat_functor' t)).
(* use (functor_composite ((X ∙ projSortToC sort _ (arr s t)) ⊗ (X ∙ projSortToC sort _ s)) *)
(*                        (hat_functor' t)). *)
(* use (((X ∙ projSortToC sort _ (arr s t)) ⊗ (X ∙ projSortToC sort s)) ∙ hat_functor sort t). *)
Defined.

(** The application constructor *)
Definition app_map (s t : sort) : sortToSet2⟦app_source s t STLC,STLC⟧.
Proof.
exact (CoproductIn _ _
   (Coproducts_functor_precat _ sortToSet sortToSet
     (Coproducts_functor_precat _ (path_pregroupoid sort) SET
        (CoproductsHSET _ _) _) _ _) (ii1 (s,, t)) · BinCoproductIn2 _ (CSortToSet2 _ _) · STLC_mor).
Defined.

(** The source of the lambda constructor *)
Definition lam_source (s t : sort) : functor sortToSet2 sortToSet2.
Proof.
exact (((pre_composition_functor (homset_property _) (homset_property _) (sorted_option_functor' s)) ∙ (post_composition_functor (homset_property _) _ (projSortToC sort _ t))) ∙ post_composition_functor (homset_property _) (homset_property _) (hat_functor' (arr s t))).
(* use (functor_composite _ (hat_functor' (arr s t))). *)
(* use (functor_composite (functor_composite (sorted_option_functor' s) X) (projSortToC sort _ t)). *)
(* use ((sorted_option_functor sort s ∙ X ∙ proj_functor sort t) ∙ hat_functor sort (arr s t)). *)
Defined.

Definition lam_map (s t : sort) : sortToSet2⟦lam_source s t STLC,STLC⟧.
Proof.
exact (CoproductIn _ _ (Coproducts_functor_precat _ sortToSet sortToSet
     (Coproducts_functor_precat _ (path_pregroupoid sort) SET
        (CoproductsHSET _ _) _) _ _) (ii2 (s,,t)) · BinCoproductIn2 _ (CSortToSet2 _ _) · STLC_mor).
Defined.

Definition make_STLC_Algebra X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
    algebra_ob STLC_Functor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ _ fvar).
use CoproductArrow.
intro b; induction b as [st|st]; induction st as [s t].
- apply (fapp s t).
- apply (flam s t).
Defined.

(** The recursor for the stlc *)
Definition foldr_map X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
  algebra_mor _ STLC_alg (make_STLC_Algebra X fvar fapp flam).
Proof.
apply (InitialArrow STLC_Functor_Initial (make_STLC_Algebra X fvar fapp flam)).
Defined.


(* TODO: the following are quite slow and the proofs are not so nice *)

(** The equation for variables *)
Lemma foldr_var X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 _ (BinCoproducts_functor_precat _ _ _ _ _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
apply id_left.
Defined.

Lemma foldr_app X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  app_map s t · foldr_map X fvar fapp flam =
  # (pr1 (app_source s t)) (foldr_map X fvar fapp flam) · fapp s t.
Proof.
  assert (p := algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam)).
  set (A I h x := (Coproducts_functor_precat I sortToSet sortToSet
     (Coproducts_functor_precat _ (path_pregroupoid sort) SET
        (CoproductsHSET _ h) _) (homset_property _) x)).
set (F := maponpaths (λ x, CoproductIn _ _
   (A _ _ _) (ii1 (s,, t)) · BinCoproductIn2 _ (CSortToSet2 _ _) · x) p).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
eapply @cancel_postcomposition.
eapply @cancel_postcomposition.
use (CoproductOfArrowsIn _ _ (A _ _ (λ _, _))).
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|].
rewrite <- assoc.
eapply pathscomp0; eapply maponpaths.
  exact (CoproductInCommutes _ _ _ _ _ _ (ii1 (s,,t))).
apply idpath.
Qed.

Lemma foldr_lam X (fvar : sortToSet2⟦1,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  lam_map s t · foldr_map X fvar fapp flam =
  # (pr1 (lam_source s t)) (foldr_map X fvar fapp flam) · flam s t.
Proof.
  assert (p := algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam)).
  set (A I h x := (Coproducts_functor_precat I sortToSet sortToSet
     (Coproducts_functor_precat _ (path_pregroupoid sort) SET
        (CoproductsHSET _ h) _) (homset_property _) x)).
set (F := maponpaths (λ x, CoproductIn _ _
   (A _ _ _) (ii2 (s,, t)) · BinCoproductIn2 _ (CSortToSet2 _ _) · x) p).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
eapply @cancel_postcomposition.
eapply @cancel_postcomposition.
use (CoproductOfArrowsIn _ _ (A _ _ (λ _, _))).
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|].
rewrite <- assoc.
eapply pathscomp0; eapply maponpaths.
  exact (CoproductInCommutes _ _ _ _ _ _ (ii2 (s,,t))).
apply idpath.
Qed.

End Lam.
