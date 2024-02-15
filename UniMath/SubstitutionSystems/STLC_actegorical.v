(**

Syntax of the simply typed lambda calculus as a
multisorted signature.

Written by: Ralph Matthes, 2024 (adapted from STLC_alt.v)

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.


Local Open Scope cat.

Section A.

  Context (sort : hSet) (arr : sort → sort → sort).

  Local Lemma Hsort : isofhlevel 3 sort.
  Proof.
    exact (isofhlevelssnset 1 sort (setproperty sort)).
  Defined.

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].


(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
(* Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)).
Local Notation "'1'" := (TerminalObject TerminalSortToSet).
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).*)

Let sortToSet2 := [sortToHSET,sortToHSET].

(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set.
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,(s ⇒ t)).
Defined.

(** the canonical functor associated with STLC_Sig *)
Definition STLC_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET STLC_Sig.

(** the canonical strength associated with STLC_Sig *)
Let θSTLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET STLC_Sig.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for STLC *)
Let σind : SigmaMonoid θSTLC := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort STLC_Sig.
Let σcoind : SigmaMonoid θSTLC := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort STLC_Sig.

Section IndAndCoind.

  Context (σ : SigmaMonoid θSTLC).

  (** the functor representing the syntax for STLC *)
  Definition STLC_gen : sortToSet2 := SigmaMonoid_carrier θSTLC σ.

  (** variable inclusion for syntax for STLC *)
  Definition STLC_eta_gen : sortToSet2⟦Id,STLC_gen⟧ := SigmaMonoid_η θSTLC σ.

  (** the algebra maps (the "domain-specific constructors") for STLC *)
  Definition STLC_tau_gen : STLC_Functor_H STLC_gen --> STLC_gen  := SigmaMonoid_τ θSTLC σ.

  (** the individual sorted constructors for application and lambda-abstraction *)

  (* TODO *)

End IndAndCoind.

Definition STLC_ind : sortToSet2 := STLC_gen σind.
Definition STLC_coind : sortToSet2 := STLC_gen σcoind.

Definition STLC_eta_ind : sortToSet2⟦Id,STLC_ind⟧ := STLC_eta_gen σind.
Definition STLC_eta_coind : sortToSet2⟦Id,STLC_coind⟧ := STLC_eta_gen σcoind.

Definition STLC_tau_ind : STLC_Functor_H STLC_ind --> STLC_ind  := SigmaMonoid_τ θSTLC σind.
Definition STLC_tau_coind : STLC_Functor_H STLC_coind --> STLC_coind  := SigmaMonoid_τ θSTLC σcoind.

End A.
