(**

Simply typed lambda calculus

Written by: Anders Mörtberg, 2017

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
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
Require Import UniMath.CategoryTheory.Monads.
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
Require Import UniMath.SubstitutionSystems.MultiSorted.

Local Open Scope cat.

Section Lam.

(** A lot of notations and preliminary definitions *)

Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
(* Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET]. *)
(* Local Notation "'Id'" := (functor_identity _). *)
(* Local Notation "F * G" := (H HSET has_homsets_HSET HSET has_homsets_HSET BinProductsHSET F G). *)
(* Local Notation "F + G" := (BinSumOfSignatures.H _ _ _ _ BinCoproductsHSET F G). *)
(* Local Notation "'_' 'o' 'option'" := *)
(*   (ℓ (option_functor BinCoproductsHSET TerminalHSET)) (at level 10). *)

(* Local Definition has_homsets_HSET2 : has_homsets HSET2. *)
(* Proof. *)
(* apply functor_category_has_homsets. *)
(* Defined. *)

(* Local Definition BinProductsHSET2 : BinProducts HSET2. *)
(* Proof. *)
(* apply (BinProducts_functor_precat _ _ BinProductsHSET). *)
(* Defined. *)

(* Let precomp_option X := (pre_composition_functor _ _ HSET has_homsets_HSET has_homsets_HSET *)
(*                           (option_functor BinCoproductsHSET TerminalHSET) X). *)
(* Local Notation "X + 1" := (precomp_option X) (at level 50). *)


(** * The simply typed lambda calculus from a binding signature *)
Variable (sort : hSet) (arr : sort → sort → sort).

Local Notation "a + b" := (setcoprod a b) : set.

(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use mkMultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set. (* todo: fix this once level of × is fixed *)
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,arr s t) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,arr s t).
Defined.

Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_precat C X (homset_property C)).

(* Print STLC_Sig. *)

Let SET : Precategory := (HSET,,has_homsets_HSET).
Local Definition SET_over_sort : Precategory.
Proof.
exists (SET / sort).
now apply has_homsets_slice_precat.
Defined.

Let hs : has_homsets (SET / sort) := homset_property SET_over_sort.

(** The signature with strength for the lambda calculus *)
Definition STLC_Signature : Signature (SET / sort) _ _ _ :=
  MultiSortedSigToSignature sort STLC_Sig.

Let Id_H := Id_H _ hs (BinCoproducts_HSET_slice sort).

Let SET_over_sort2 := [SET/sort,SET_over_sort].

Lemma hs2 : has_homsets SET_over_sort2.
Proof.
apply functor_category_has_homsets.
Qed.

Lemma BinProducts_SET_over_sort2 : BinProducts SET_over_sort2.
Proof.
apply BinProducts_functor_precat, BinProducts_slice_precat, PullbacksHSET.
Defined.

Definition STLC_Functor : functor SET_over_sort2 SET_over_sort2 :=
  Id_H STLC_Signature.

Lemma STLC_Functor_Initial : Initial (FunctorAlg STLC_Functor hs2).
Proof.
apply SignatureInitialAlgebraSetSort.
apply is_omega_cocont_MultiSortedSigToSignature.
apply slice_precat_colims_of_shape, ColimsHSET_of_shape.
Defined.

Definition STLC_Monad : Monad (SET / sort) :=
  MultiSortedSigToMonad sort STLC_Sig.

Definition STLC : SET_over_sort2 :=
  alg_carrier _ (InitialObject STLC_Functor_Initial).

Let STLC_mor : SET_over_sort2⟦STLC_Functor STLC,STLC⟧ :=
  alg_map _ (InitialObject STLC_Functor_Initial).

Let STLC_alg : algebra_ob STLC_Functor :=
  InitialObject STLC_Functor_Initial.



Lemma foo : BinProducts [SET_over_sort,SET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Notation "'1'" := (functor_identity SET_over_sort).
Local Notation "x ⊗ y" := (BinProductObject _ (foo x y)) (at level 10).


Definition var_map : SET_over_sort2⟦1,STLC⟧ :=
  BinCoproductIn1 SET_over_sort2 _ · STLC_mor.

Definition app_source (s t : sort) (X : SET_over_sort2) : SET_over_sort2 :=
  (X ∙ proj_functor sort (arr s t)) ⊗ (X ∙ proj_functor sort s) ∙ hat_functor sort t.

Lemma Coproducts_SET_over_sort2 : Coproducts ((sort × sort) + (sort × sort))%set SET_over_sort2.
Proof.
apply Coproducts_functor_precat, Coproducts_slice_precat, CoproductsHSET.
apply setproperty.
Defined.

Definition app_map (s t : sort) : SET_over_sort2⟦app_source s t STLC,STLC⟧.
Proof.
use (CoproductIn _ _ _ (ii1 (s,,t)) · BinCoproductIn2 _ _ · STLC_mor).
Defined.

Definition lam_source (s t : sort) (X : SET_over_sort2) : SET_over_sort2 :=
  ((sorted_option_functor sort s ∙ X) ∙ proj_functor sort t) ∙ hat_functor sort (arr s t).

Definition lam_map (s t : sort) : SET_over_sort2⟦lam_source s t STLC,STLC⟧.
Proof.
use (CoproductIn _ _ _ (ii2 (s,,t)) · BinCoproductIn2 _ _ · STLC_mor).
Defined.

Definition mk_STLC_Algebra X (fvar : SET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, SET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, SET_over_sort2⟦lam_source s t X,X⟧) :
    algebra_ob STLC_Functor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ _ fvar).
use CoproductArrow.
intro b; induction b as [st|st]; induction st as [s t].
- apply (fapp s t).
- apply (flam s t).
Defined.

Definition foldr_map X (fvar : SET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, SET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, SET_over_sort2⟦lam_source s t X,X⟧) :
  algebra_mor _ STLC_alg (mk_STLC_Algebra X fvar fapp flam).
Proof.
apply (InitialArrow STLC_Functor_Initial (mk_STLC_Algebra X fvar fapp flam)).
Defined.

Lemma foldr_var X (fvar : SET_over_sort2⟦1,X⟧)
  (fapp : ∏ s t, SET_over_sort2⟦app_source s t X,X⟧)
  (flam : ∏ s t, SET_over_sort2⟦lam_source s t X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
assert (F := maponpaths (fun x => BinCoproductIn1 _ (BinCoproducts_functor_precat _ _ _ _ _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
apply id_left.
Defined.

(* (* Lemma foldr_var_pt X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) (A : HSET) (x : pr1 A) : *) *)
(* (*   pr1 (pr1 (foldr_map X fvar fapp flam)) A (pr1 var_map A x) = pr1 fvar A x. *) *)
(* (* Proof. *) *)
(* (* set (H := (toforallpaths _ _ _ (nat_trans_eq_pointwise (foldr_var X fvar fapp flam) A) x)). *) *)
(* (* (* now rewrite foldr_var. *) *) *)
(* (* (* Arguments foldr_map : simpl never. *) *) *)
(* (* (* Arguments alg_carrier : simpl never. *) *) *)
(* (* (* Arguments var_map : simpl never. *) *) *)
(* (* cbn in *. *) *)
(* (* apply H. *) *)
(* (* Qed. *) *)

(* Lemma foldr_app X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) : *)
(*   app_map · foldr_map X fvar fapp flam = *)
(*   # (pr1 (Id * Id)) (foldr_map X fvar fapp flam) · fapp. *)
(* Proof. *)
(*   assert (F := maponpaths (fun x => CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) true · *)
(*                                                 BinCoproductIn2 _ (BinCoproducts_functor_precat *)
(*                                                                      _ _ _ _ _ _) · x) *)
(*                         (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))). *)
(* rewrite assoc in F. *)
(* eapply pathscomp0; [apply F|]. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition. *)
(*   rewrite <- assoc. *)
(*   eapply maponpaths, BinCoproductOfArrowsIn2. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition, cancel_postcomposition. *)
(*   apply (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ *)
(*           (CoproductsHSET _ isasetbool) *)
(*           _ (λ i, pr1 (Arity_to_Signature has_homsets_HSET BinProductsHSET *)
(*                          BinCoproductsHSET TerminalHSET (BindingSigMap LamSig i)) `LC_alg))). *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|]. *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; eapply maponpaths. *)
(*   refine (CoproductInCommutes _ _ _ _ _ _ true). *)
(* apply idpath. *)
(* Defined. *)

(* Lemma foldr_lam X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) : *)
(*   lam_map · foldr_map X fvar fapp flam = *)
(*   # (pr1 (_ o option)) (foldr_map X fvar fapp flam) · flam. *)
(* Proof. *)
(*   assert (F := maponpaths (fun x => CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _ _) false · *)
(*                                                 BinCoproductIn2 _ (BinCoproducts_functor_precat *)
(*                                                                      _ _ _ _ _ _) · x) *)
(*                         (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))). *)
(* rewrite assoc in F. *)
(* eapply pathscomp0; [apply F|]. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition. *)
(*   rewrite <- assoc. *)
(*   eapply maponpaths, BinCoproductOfArrowsIn2. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition, cancel_postcomposition. *)
(*   apply (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ *)
(*           (CoproductsHSET _ isasetbool) *)
(*           _ (λ i, pr1 (Arity_to_Signature has_homsets_HSET BinProductsHSET *)
(*                          BinCoproductsHSET TerminalHSET (BindingSigMap LamSig i)) `LC_alg))). *)
(* rewrite <- assoc. *)
(* eapply pathscomp0. *)
(*   eapply maponpaths, BinCoproductIn2Commutes. *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; eapply maponpaths. *)
(*   refine (CoproductInCommutes _ _ _ _ _ _ false). *)
(* apply idpath. *)
(* Defined. *)


(* Local Notation "'1'" := (TerminalHSET). *)
(* Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsHSET a b)) (at level 50). *)
(* Local Notation "x ⊛ y" := (BinProductObject _ (BinProductsHSET x y)) (at level 60). *)

(* (** This makes cbn not unfold things too much below *) *)
(* Arguments LamMonad : simpl never. *)
(* Arguments BinCoproductObject : simpl never. *)

(* Definition substLam (X : HSET) : HSET⟦LamMonad (X ⊕ 1) ⊛ LamMonad X,LamMonad X⟧. *)
(* Proof. *)
(* intro H. *)
(* set (f := monadSubst LamMonad TerminalHSET BinCoproductsHSET X). *)
(* set (g := λ (_ : unit), pr2 H). *)
(* cbn in H, f, g. *)
(* apply (f g (pr1 H)). *)
(* Defined. *)

End Lam.
