(**************************************************************************************************

  The free theory

  This file defines the free functor from sets to algebraic theories, and shows that it is left
  adjoint to the forgetful functor. The free algebraic theory on set X is the theory with just
  constants (taken from X) and variables. The category of algebras for the free theory on X
  is equivalent to the coslice category X ↓ SET.

  Contents
  1. The free functor [free_functor]
  2. The forgetful functor [forgetful_functor]
  3. The adjunction [free_functor_is_free]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The free functor *)

Definition free_theory'_data (X : hSet) : algebraic_theory'_data.
Proof.
  use make_algebraic_theory'_data.
  - intro n.
    exact (setcoprod (stnset n) X).
  - exact (λ _ i, inl i).
  - intros m n f g.
    induction f as [f' | f'].
    + exact (g f').
    + exact (inr f').
Defined.

Definition free_is_theory' {X : hSet} : is_algebraic_theory' (free_theory'_data X).
Proof.
  use make_is_algebraic_theory'.
  - now do 4 intro.
  - do 2 intro.
    now induction f.
  - intros l m n f_l f_m f_n.
    now induction f_l.
Qed.

Definition free_theory (X : hSet) : algebraic_theory
  := make_algebraic_theory' _ (free_is_theory' (X := X)).

Definition free_functor_morphism_data
  {X X' : hSet}
  (f : X → X')
  : algebraic_theory_morphism'_data (free_theory X) (free_theory X').
Proof.
  intros n x.
  induction x as [left | right].
  - exact (inl left).
  - exact (inr (f right)).
Defined.

Lemma free_functor_is_morphism
  {X X' : hSet}
  (f : X → X')
  : is_algebraic_theory_morphism' (free_functor_morphism_data f).
Proof.
  use make_is_algebraic_theory_morphism'.
  - intros m n s t.
    now induction s.
  - intros n t.
    now induction t.
Qed.

Definition free_functor_data
  : functor_data SET algebraic_theory_cat
  := make_functor_data (C := SET) (C' := algebraic_theory_cat)
    (λ X, free_theory X)
    (λ X X' f, (make_algebraic_theory_morphism' _ (free_functor_is_morphism f))).

Lemma free_functor_is_functor
  : is_functor free_functor_data.
Proof.
  split.
  - intro A.
    use (algebraic_theory_morphism_eq (T := free_theory A) (T' := free_theory A)).
    intros n f.
    now induction f.
  - intros a b c d e.
    use (algebraic_theory_morphism_eq (T := free_theory a) (T' := free_theory c)).
    intros n f.
    now induction f.
Qed.

Definition free_functor : HSET ⟶ algebraic_theory_cat
  := make_functor _ free_functor_is_functor.

(** * 2. The forgetful functor *)

Definition forgetful_functor_data : functor_data algebraic_theory_cat HSET.
Proof.
  use make_functor_data.
  - intro T.
    exact ((T : algebraic_theory) 0).
  - intros T T' F.
    exact ((F : algebraic_theory_morphism T T') 0).
Defined.

Lemma forgetful_is_functor : is_functor forgetful_functor_data.
Proof.
  use tpair;
    easy.
Qed.

Definition forgetful_functor : algebraic_theory_cat ⟶ HSET
  := make_functor _ forgetful_is_functor.

(** * 3. The adjunction *)

Lemma lift_constant_eq
  (T : algebraic_theory)
  {n : nat}
  (f f' : (T 0 : hSet))
  (g : stn 0 → (T n : hSet))
  (H : f = f')
  : lift_constant n f = f' • g.
Proof.
  induction H.
  refine (maponpaths (comp f) _).
  apply funextfun.
  intro x.
  apply fromempty.
  exact (negnatlthn0 _ (stnlt x)).
Qed.

Section Adjunction.

  Context (A : hSet).
  Context (T : algebraic_theory).

  Definition theory_morphism_to_function
    (F : algebraic_theory_morphism (free_theory A) T)
    : A → (forgetful_functor T : hSet)
    := λ a, F 0 (inr a).

  Definition function_to_theory_morphism'_data
    (F : A → (forgetful_functor T : hSet))
    : algebraic_theory_morphism'_data (free_theory A) T.
  Proof.
    intros ? f.
    induction f as [i | a].
    - exact (pr i).
    - exact (lift_constant _ (F a)).
  Defined.

  Lemma function_to_is_theory_morphism'
    (F : A → (forgetful_functor T : hSet))
    : is_algebraic_theory_morphism' (function_to_theory_morphism'_data F).
  Proof.
    use make_is_algebraic_theory_morphism'.
    - intros ? ? f ?.
      induction f.
      + exact (!algebraic_theory_comp_projects_component _ _ _ _ _).
      + refine (lift_constant_eq _ _ _ _ (idpath _) @ !_).
        apply algebraic_theory_comp_is_assoc.
    - easy.
  Qed.

  Definition function_to_theory_morphism
    (F : A → (forgetful_functor T : hSet))
    : algebraic_theory_morphism (free_theory A) T
    := make_algebraic_theory_morphism' _ (function_to_is_theory_morphism' F).

  Lemma invweqweq
    (F : algebraic_theory_morphism (free_theory A) T)
    : function_to_theory_morphism (theory_morphism_to_function F) = F.
  Proof.
    apply algebraic_theory_morphism_eq.
    intros ? f.
    induction f.
    - exact (!algebraic_theory_morphism_preserves_projections _ _).
    - refine (lift_constant_eq _ _ _ _ (idpath _) @ _).
      exact (!algebraic_theory_morphism_preserves_composition F _ _ _ _
        : _ = F _ (lift_constant _ _)).
  Qed.

  Lemma weqinvweq
    (F : A → (forgetful_functor T : hSet))
    : theory_morphism_to_function (function_to_theory_morphism F) = F.
  Proof.
    apply funextfun.
    intro.
    refine (lift_constant_eq _ _ _ _ (idpath _) @ _).
    exact (algebraic_theory_comp_identity_projections _ _ _).
  Qed.

End Adjunction.

Definition free_functor_is_free
  : are_adjoints free_functor forgetful_functor.
Proof.
  use adj_from_nathomweq.
  use tpair.
  - refine (λ A (T : algebraic_theory), _).
    use weq_iso.
    + exact (theory_morphism_to_function A T).
    + exact (function_to_theory_morphism A T).
    + exact (invweqweq A T).
    + exact (weqinvweq A T).
  - abstract (
      use tpair;
      easy
    ).
Defined.
