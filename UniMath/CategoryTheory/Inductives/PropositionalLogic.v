(**

This file contains a formalization of the syntax of propositional logic as the initial algebra of a
functor.

Following Goldblatt's 'Topoi', all of the connectives are treated as primitive. As stated there,
they are _a priori_ distinct; their interdefinability is naturally propositional, not definitional.

Written by: Langston Barrett, 2019

*)

(** ** Contents

  - Definition of PL syntax as an initial algebra
  - Definition of a PL valuation in [bool]
  - TODO: Definition of a PL valuation in an (order-theoretic) algebra
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.

Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.

Local Open Scope cat.
Local Open Scope cocont_functor_hset_scope.

Section PL.

Let times x y := BinProductObject _ (BinProductsHSET x y).
Local Infix "⊗" := times.

Variable (vars : hSet).

(**
  <<
    PL_functor Var Rec :=
        Var            (* -- arity 1, sentences *)
      + Rec            (* -- arity 1, ¬ (not) *)
      + (Rec × Rec)    (* -- arity 2, ∧ (and) *)
      + (Rec × Rec)    (* -- arity 2, ∨ (or) *)
      + (Rec × Rec)    (* -- arity 2, → (implies) *)
   >>
 *)
Definition PL_functor : omega_cocont_functor HSET HSET :=
  ' vars + Id + (Id * Id) + (Id * Id) + (Id * Id).

Definition PL_functor' : functor HSET HSET := pr1 PL_functor.

Lemma PL_functor_initial :
  Initial (precategory_FunctorAlg PL_functor' has_homsets_HSET).
Proof.
  apply (colimAlgInitial _ InitialHSET (pr2 PL_functor) (ColimCoconeHSET _ _)).
Defined.

Let PL_alg : algebra_ob PL_functor' := InitialObject PL_functor_initial.

(** The underlying set of the initial algebra *)
Definition PL : hSet := alg_carrier _ PL_alg.

Definition PL_type : UU := pr1hSet PL.

Definition PL_var : HSET⟦vars, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro v; do 4 apply inl; exact v.
Defined.

Definition PL_not : HSET⟦PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; do 3 apply inl; apply inr; exact s.
Defined.

Definition PL_and : HSET⟦PL ⊗ PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; do 2 apply inl; apply inr; exact s.
Defined.

Definition PL_and_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_and (dirprodpair x y).

Definition PL_or : HSET⟦PL ⊗ PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; do 1 apply inl; apply inr; exact s.
Defined.

Definition PL_or_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_or (dirprodpair x y).

Definition PL_impl : HSET⟦PL ⊗ PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; do 1 apply inl; apply inr; exact s.
Defined.

Definition PL_impl_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_impl (dirprodpair x y).

Definition PL_iff_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_and_fun (PL_impl (dirprodpair x y)) (PL_impl (dirprodpair y x)).

Delimit Scope PL with PL.
Notation "¬" := (PL_not) : PL.
Infix "∧" := (PL_and) : PL.
Infix "∨" := (PL_or) : PL.
Infix "⇒" := (PL_impl) : PL.
Infix "⇔" := (PL_iff_fun) (at level 90) : PL.

Definition PL_mk_algebra (X : hSet) (vs : vars -> X) (not : X -> X)
           (and : X -> X -> X) (or : X -> X -> X) (impl : X -> X -> X) :
  algebra_ob PL_functor'.
Proof.
  exists X.
  cbn; do 5 (try (apply sumofmaps)).
  - assumption. (* vs *)
  - exact not.
  - apply (invweq (weqfunfromdirprod _ _ _)); exact and.
  - apply (invweq (weqfunfromdirprod _ _ _)); exact or.
  - apply (invweq (weqfunfromdirprod _ _ _)); exact impl.
Defined.

(** The fold, or catamorphism: given the same structure of operations on any
    other set, we can construct an interpretation of PL in that set. *)
(** TODO: why are the pr1s necessary? *)
Definition PL_fold (X : hSet) (vs : vars -> X)
           (not : X -> X) (and : X -> X -> X) (or : X -> X -> X) (impl : X -> X -> X) :
  PL -> X.
Proof.
  apply (InitialArrow PL_functor_initial (PL_mk_algebra X vs not and or impl)).
Defined.

End PL.

(** A valuation for atomic sentences can be extended to one for all sentences. *)
Definition bool_valuation {vars : hSet} (V : vars -> bool) : PL vars -> bool.
Proof.
  use (PL_fold vars (hSetpair _ isasetbool)).
  - assumption. (* V *)
  - exact negb.
  - exact andb.
  - exact orb.
  - exact implb.
Defined.
