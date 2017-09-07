
(** Interface file to the package SubstitutionSystems *)

(**
  The purpose of this file is to provide a stable interface to
  the formalization of heterogeneous substitution systems as
  defined by Matthes and Uustalu

  PLEASE DO NOT RENAME THIS FILE - its name is referenced in
  an article about this formalization

  TODO: provide reference to the article/preprint

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.Notation.

Notation "⦃ f ⦄" := (fbracket _ f)(at level 0).
Notation "G • F" := (functor_composite F G).



(** * Generalized Iteration in Mendler-style and fusion law *)

(** Lemma 8 *)

Definition GenMendlerIteration :
   ∏ (C : precategory) (hsC : has_homsets C) (F : functor C C)
   (μF_Initial : Initial (FunctorAlg F hsC)) (C' : precategory)
   (hsC' : has_homsets C') (X : C') (L : functor C C'),
   Adjunctions.is_left_adjoint L
   → ∏ ψ : ψ_source C C' hsC' X L ⟹ ψ_target C F C' hsC' X L,
     ∃! h : C' ⟦ L ` (InitialObject μF_Initial), X ⟧,
     # L (alg_map F (InitialObject μF_Initial)) · h =
     ψ ` (InitialObject μF_Initial) h.
Proof.
  simpl.
  apply GenMendlerIteration.
Defined.

Arguments It {_ _ _} _ {_} _ _ _ _ _ .

(** Lemma 9 *)

Theorem fusion_law
     : ∏ (C : precategory) (hsC : has_homsets C)
       (F : functor C C)
       (μF_Initial : Initial (precategory_FunctorAlg F hsC))
       (C' : precategory) (hsC' : has_homsets C')
       (X X' : C') (L : functor C C')
       (is_left_adj_L : Adjunctions.is_left_adjoint L)
       (ψ : ψ_source C C' hsC' X L ⟹ ψ_target C F C' hsC' X L)
       (L' : functor C C')
       (is_left_adj_L' : Adjunctions.is_left_adjoint L')
       (ψ' : ψ_source C C' hsC' X' L' ⟹ ψ_target C F C' hsC' X' L')
       (Φ : yoneda_objects C' hsC' X • functor_opp L
              ⟹
            yoneda_objects C' hsC' X' • functor_opp L'),
       let T:= (` (InitialObject μF_Initial)) in
       ψ T · Φ (F T) = Φ T · ψ' T
       →
       Φ T (It μF_Initial hsC' X L is_left_adj_L ψ) =
       It μF_Initial hsC' X' L' is_left_adj_L' ψ'.
Proof.
  apply fusion_law.
Qed.


(** * Heterogeneous Substitution Systems *)

(** Lemma 15 *)

Lemma fbracket_natural
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (H : Signature C hs C hs) (T : hss CP H) (Z Z' : precategory_Ptd C hs)
       (f : precategory_Ptd C hs ⟦ Z, Z' ⟧)
       (g : precategory_Ptd C hs ⟦ Z', ptd_from_alg T ⟧),
       (`T ∘ # U f : [C,C,hs] ⟦ `T • U Z , `T • U Z' ⟧) · ⦃ g ⦄ = ⦃ f · g ⦄ .
Proof.
  apply fbracket_natural.
Qed.

Lemma compute_fbracket
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (H : Signature C hs C hs) (T : hss CP H) (Z : precategory_Ptd C hs)
       (f : precategory_Ptd C hs ⟦ Z, ptd_from_alg T ⟧),
       ⦃ f ⦄ = (`T ∘ # U f : [C,C,hs] ⟦ `T • U Z , `T • U _ ⟧) · ⦃ identity (ptd_from_alg T) ⦄.
Proof.
  apply compute_fbracket.
Qed.


(** * Monads from hss *)

(** Theorem 24 *)

Definition Monad_from_hss
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (H : Signature C hs C hs), hss CP H → Monad C.
Proof.
  apply Monad_from_hss.
Defined.

(** Theorem 25 *)

Definition hss_to_monad_functor
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (H : Signature C hs C hs),
       functor (hss_precategory CP H) (precategory_Monad C hs).
Proof.
  apply hss_to_monad_functor.
Defined.

(** Lemma 26 *)

Lemma faithful_hss_to_monad
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (H : Signature C hs C hs), faithful (hss_to_monad_functor C hs CP H).
Proof.
  apply faithful_hss_to_monad.
Defined.


(** * Lifting initiality *)

(** Theorem 28 in three steps:
    - the operation itself
    - its compatibility with variables
    - its compatibility with signature-dependent constructions
*)

Definition bracket_for_initial_algebra
 : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C),
     (∏ Z : precategory_Ptd C hs, GlobalRightKanExtensionExists C C (U Z) C hs hs)
       → ∏ (H : Signature C hs C hs)
           (IA : Initial (FunctorAlg (Id_H C hs CP H) (functor_category_has_homsets C C hs)))
           (Z : precategory_Ptd C hs),
           precategory_Ptd C hs ⟦ Z, ptd_from_alg (InitAlg C hs CP H IA) ⟧
           →
           [C, C, hs] ⟦ ℓ (U Z) ` (InitialObject IA), ` (InitAlg C hs CP H IA) ⟧.
Proof.
  apply bracket_Thm15.
Defined.

Lemma bracket_Thm15_ok_η
     : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
       (KanExt : ∏ Z : precategory_Ptd C hs,
                 GlobalRightKanExtensionExists C C (U Z) C hs hs)
       (H : Signature C hs C hs)
       (IA : Initial (FunctorAlg (Id_H C hs CP H) (functor_category_has_homsets C C hs)))
       (Z : precategory_Ptd C hs)
       (f : precategory_Ptd C hs ⟦ Z, ptd_from_alg (InitAlg C hs CP H IA)⟧),
       # U f =
       # (pr1 (ℓ (U Z))) (η (InitAlg C hs CP H IA)) ·
       bracket_Thm15 C hs CP KanExt H IA Z f.
Proof.
  apply bracket_Thm15_ok_part1.
Qed.

Lemma bracket_Thm15_ok_τ
  : ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C)
      (KanExt : ∏ Z : precategory_Ptd C hs, GlobalRightKanExtensionExists C C (U Z) C hs hs)
      (H : Signature C hs C hs)
      (IA : Initial (FunctorAlg (Id_H C hs CP H) (functor_category_has_homsets C C hs)))
      (Z : precategory_Ptd C hs)
      (f : precategory_Ptd C hs ⟦ Z, ptd_from_alg (InitAlg C hs CP H IA) ⟧),
    (theta H) (` (InitAlg C hs CP H IA) ⊗ Z) ·
    # H (bracket_Thm15 C hs CP KanExt H IA Z f) ·
    τ (InitAlg C hs CP H IA)
    =
    # (pr1 (ℓ (U Z))) (τ (InitAlg C hs CP H IA)) ·
      bracket_Thm15 C hs CP KanExt H IA Z f.
Proof.
  apply bracket_Thm15_ok_part2.
Qed.

(** Theorem 29 *)

Definition Initial_HSS :
   ∏ (C : precategory) (hs : has_homsets C) (CP : BinCoproducts C),
     (∏ Z : precategory_Ptd C hs,
         GlobalRightKanExtensionExists C C (U Z) C hs hs)
     → ∏ H : Signature C hs C hs,
       Initial (FunctorAlg (Id_H C hs CP H) (functor_category_has_homsets C C hs))
       → Initial (hss_precategory CP H).
Proof.
  apply InitialHSS.
Defined.


(** * Sum of signatures *)

(** Lemma 30 *)

Definition Sum_of_Signatures
  : ∏ (C : precategory) (hsC : has_homsets C)(D : precategory) (hs : has_homsets D),
       BinCoproducts D → Signature C hsC D hs → Signature C hsC D hs → Signature C hsC D hs.
Proof.
  apply BinSum_of_Signatures.
Defined.


(** * Arities of signatures for lambda calculus *)

(** Definition 31 *)

Definition App_Sig
  : ∏ (C : precategory) (hs : has_homsets C), BinProducts C → Signature C hs C hs.
Proof.
  apply App_Sig.
Defined.

(** Definition 32 *)

Definition Lam_Sig
  : ∏ (C : precategory) (hs : has_homsets C),
    Terminal C → BinCoproducts C → BinProducts C → Signature C hs C hs.
Proof.
  apply Lam_Sig.
Defined.

(** Definition 33 *)

Definition Flat_Sig
  : ∏ (C : precategory) (hs : has_homsets C), Signature C hs C hs.
Proof.
  apply Flat_Sig.
Defined.

(** * Evaluation of explicit substitution as initial morphism *)

(** Definition 36 *)

Definition Lam_Flatten
  :  ∏ (C : precategory) (hs : has_homsets C)
       (terminal : Terminal C)
       (CC : BinCoproducts C) (CP : BinProducts C),
    (∏ Z : precategory_Ptd C hs,
        GlobalRightKanExtensionExists C C (U Z) C hs hs)
    → ∏ Lam_Initial : Initial (FunctorAlg (Id_H C hs CC (Lam_Sig C hs terminal CC CP))
                                          (functor_category_has_homsets C C hs)),
  [C, C, hs] ⟦ (Flat_H C hs) ` (InitialObject Lam_Initial), ` (InitialObject Lam_Initial) ⟧.
Proof.
  apply Lam_Flatten.
Defined.

(** Lemma 37, construction of the bracket *)

Definition fbracket_for_LamE_algebra_on_Lam
  : ∏ (C : precategory) (hs : has_homsets C) (terminal : Terminal C)
      (CC : BinCoproducts C) (CP : BinProducts C)
      (KanExt : ∏ Z : precategory_Ptd C hs, GlobalRightKanExtensionExists C C (U Z) C hs hs)
      (Lam_Initial : Initial (FunctorAlg (Id_H C hs CC (Lam_Sig C hs terminal CC CP))
                                         (functor_category_has_homsets C C hs)))
      (Z : precategory_Ptd C hs),
    precategory_Ptd C hs ⟦ Z ,
                           (ptd_from_alg_functor CC (LamE_Sig C hs terminal CC CP))
                             (LamE_algebra_on_Lam C hs terminal CC CP KanExt Lam_Initial) ⟧
    → [C, C, hs]
             ⟦ functor_composite (U Z)
                                 ` (LamE_algebra_on_Lam C hs terminal CC CP KanExt Lam_Initial),
               ` (LamE_algebra_on_Lam C hs terminal CC CP KanExt Lam_Initial) ⟧.
Proof.
  apply fbracket_for_LamE_algebra_on_Lam.
Defined.

(** Morphism from initial hss to construed hss, consequence of Lemma 37 *)

Definition EVAL
  : ∏ (C : precategory) (hs : has_homsets C) (terminal : Terminal C)
      (CC : BinCoproducts C) (CP : BinProducts C)
      (KanExt : ∏ Z : precategory_Ptd C hs, GlobalRightKanExtensionExists C C (U Z) C hs hs)
       (Lam_Initial : Initial
                        (FunctorAlg
                           (Id_H C hs CC
                              (LamSignature.Lam_Sig C hs terminal CC CP))
                           (functor_category_has_homsets C C hs)))
       (LamE_Initial : Initial
                         (FunctorAlg
                            (Id_H C hs CC (LamE_Sig C hs terminal CC CP))
                            (functor_category_has_homsets C C hs))),
       hss_precategory CC (LamE_Sig C hs terminal CC CP)
                       ⟦ InitialObject
                           (LamEHSS_Initial C hs terminal CC CP KanExt LamE_Initial),
                         LamE_model_on_Lam C hs terminal CC CP KanExt Lam_Initial ⟧.
Proof.
  apply FLATTEN.
Defined.
