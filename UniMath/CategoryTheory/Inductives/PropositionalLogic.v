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
  (omega_cocont_constant_functor (vars : HSET)) + Id + (Id * Id) + (Id * Id) + (Id * Id).

(*
Definition PL_functor : omega_cocont_functor HSET HSET :=
  ' vars + Id + (Id * Id) + (Id * Id) + (Id * Id).
 *)

(** The following three statements are crucial for performance. *)
Definition PL_functor' : functor HSET HSET := pr1 PL_functor.
Let is_omega_cocont_PL_functor' : is_omega_cocont PL_functor' := pr2 PL_functor.
Opaque is_omega_cocont_PL_functor'.

Lemma PL_functor_initial :
  Initial (category_FunctorAlg PL_functor').
Proof.
  apply (colimAlgInitial InitialHSET is_omega_cocont_PL_functor' (ColimCoconeHSET _ _)).
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
  PL_and (make_dirprod x y).

Definition PL_or : HSET⟦PL ⊗ PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; do 1 apply inl; apply inr; exact s.
Defined.

Definition PL_or_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_or (make_dirprod x y).

Definition PL_impl : HSET⟦PL ⊗ PL, PL⟧.
  refine (_ · alg_map _ PL_alg).
  intro s; apply inr; exact s.
Defined.

Definition PL_impl_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_impl (make_dirprod x y).

Definition PL_iff_fun (x : PL_type) (y : PL_type) : PL_type :=
  PL_and_fun (PL_impl (make_dirprod x y)) (PL_impl (make_dirprod y x)).

Declare Scope PL.
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
Definition PL_fold_alg_mor {X : hSet} (vs : vars -> X)
           (not : X -> X) (and : X -> X -> X) (or : X -> X -> X) (impl : X -> X -> X) :
  algebra_mor PL_functor' PL_alg (PL_mk_algebra X vs not and or impl).
Proof.
  apply (InitialArrow PL_functor_initial (PL_mk_algebra X vs not and or impl)).
Defined.

Definition PL_fold {X : hSet} (vs : vars -> X)
           (not : X -> X) (and : X -> X -> X) (or : X -> X -> X) (impl : X -> X -> X) :
  PL -> X := mor_from_algebra_mor _ _ _ (PL_fold_alg_mor vs not and or impl).

(** Some lemmas expressing the computational behavior of [PL_fold] *)
Section FoldComputationLemmas.
  Context {X : hSet} (vs : vars -> X)
          (not : X -> X) (and : X -> X -> X) (or : X -> X -> X) (impl : X -> X -> X).

  Let fold := PL_fold vs not and or impl.
  Let mor := PL_fold_alg_mor vs not and or impl.
  Let comm := algebra_mor_commutes _ _ _ mor.

  Lemma PL_fold_var : ∏ z, fold (PL_var z) = vs z.
  Proof.
    reflexivity.
  Qed.

  Lemma PL_fold_not : ∏ p, fold (PL_not p) = not (fold p).
  Proof.
    intro.
    do 3 apply (maponpaths (λ x, (inl : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply (maponpaths (λ x, (inr : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply eqtohomot in comm.
    specialize (comm p).
    exact comm.
  Qed.

  Lemma PL_fold_and : ∏ p q, fold (PL_and (make_dirprod p q)) = and (fold p) (fold q).
  Proof.
    intros p q.
    do 2 apply (maponpaths (λ x, (inl : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply (maponpaths (λ x, (inr : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply eqtohomot in comm.
    specialize (comm (make_dirprod p q)).
    exact comm.
  Qed.

  Lemma PL_fold_or : ∏ p q, fold (PL_or (make_dirprod p q)) = or (fold p) (fold q).
  Proof.
    intros p q.
    apply (maponpaths (λ x, (inl : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply (maponpaths (λ x, (inr : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply eqtohomot in comm.
    specialize (comm (make_dirprod p q)).
    exact comm.
  Qed.

  Lemma PL_fold_impl : ∏ p q, fold (PL_impl (make_dirprod p q)) = impl (fold p) (fold q).
  Proof.
    intros p q.
    apply (maponpaths (λ x, (inr : HSET ⟦_, BinCoproductsHSET _ _⟧) · x)) in comm.
    apply eqtohomot in comm.
    specialize (comm (make_dirprod p q)).
    apply comm.
  Qed.
End FoldComputationLemmas.


(** The induction principle.

    Mirrors the proof for lists.
 *)
Section PL_ind.

Context {P : PL -> UU} (PhSet : ∏ l, isaset (P l)).
Context (P_vars : ∏ v : vars, P (PL_var v))
        (P_not : ∏ pl, P pl -> P (PL_not pl))
        (P_and : ∏ pl1 pl2, P pl1 -> P pl2 -> P (PL_and (make_dirprod pl1 pl2)))
        (P_or : ∏ pl1 pl2, P pl1 -> P pl2 -> P (PL_or (make_dirprod pl1 pl2)))
        (P_impl : ∏ pl1 pl2, P pl1 -> P pl2 -> P (PL_impl (make_dirprod pl1 pl2))).

Let P' : UU := ∑ pl : PL, P pl.
Let P'_vars (v : vars) : P' := (PL_var v,, P_vars v).
Let P'_not (pl : P') : P' := (PL_not (pr1 pl),, P_not _ (pr2 pl)).
Let P'_and (pl1 pl2 : P') : P' :=
  (PL_and (make_dirprod (pr1 pl1) (pr1 pl2)),,
   P_and _ _ (pr2 pl1) (pr2 pl2)).
Let P'_or (pl1 pl2 : P') : P' :=
  (PL_or (make_dirprod (pr1 pl1) (pr1 pl2)),,
   P_or _ _ (pr2 pl1) (pr2 pl2)).
Let P'_impl (pl1 pl2 : P') : P' :=
  (PL_impl (make_dirprod (pr1 pl1) (pr1 pl2)),,
   P_impl _ _ (pr2 pl1) (pr2 pl2)).

Definition P'HSET : HSET.
Proof.
  use make_hSet.
  - exact P'.
  - abstract (apply (isofhleveltotal2 2); [ apply setproperty | intro x; apply PhSet ]).
Defined.

Opaque is_omega_cocont_PL_functor'.

Lemma is_algebra_morphism_pr1_PL_fold :
  is_algebra_mor _ PL_alg PL_alg (λ l, pr1 (@PL_fold P'HSET P'_vars P'_not P'_and P'_or P'_impl l)).
Proof.
apply (BinCoproductArrow_eq_cor _ BinCoproductsHSET).
- apply funextfun; intro x; induction x as [x2 | x3].
  + induction x2 as [x4 | x5].
    * induction x4 as [x6 | x7].
      -- cbn in x6.
         (* This line takes forever, more performance work to be done. *)
         (* apply (maponpaths pr1 (@PL_fold_var P'HSET P'_vars P'_not P'_and P'_or P'_impl x6)). *)
Abort.

End PL_ind.

End PL.

(** A valuation for atomic sentences can be extended to one for all sentences. *)
Definition bool_valuation {vars : hSet} (V : vars -> bool) : PL vars -> bool.
Proof.
  use (@PL_fold vars boolset).
  - assumption. (* V *)
  - exact negb.
  - exact andb.
  - exact orb.
  - exact implb.
Defined.
