(*
  Shows that, given an algebraic theory T, there is an equivalence between its algebras and tuples
  of a set X and a morphism from T to the endomorphism theory on X.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.

(* Definition algebra_to_algebraic_theory_morphism'_data
  {T : algebraic_theory}
  (X : algebraic_theory_algebra T)
  : algebraic_theory_morphism'_data T (set_endomorphism_theory X).
Proof.
  pose (@action T X).
  intros n f.

  simpl.
  := @action T X.

Lemma algebra_to_is_algebraic_theory_morphism'
  {T : algebraic_theory}
  (X : algebraic_theory_algebra T)
  : is_algebraic_theory_morphism' (algebra_to_algebraic_theory_morphism'_data X).
Proof.
  use make_is_algebraic_theory_morphism'.
  - do 4 intro.
    apply funextfun.
    intro.
    apply algebraic_theory_algebra_is_assoc.
  - intros n i.
    apply funextfun.
    intro.
    apply (algebraic_theory_algebra_projects_component _ _ i).
Qed.

Definition algebra_to_algebraic_theory_morphism
  {T : algebraic_theory}
  (X : algebraic_theory_algebra T)
  : algebraic_theory_morphism T (set_endomorphism_theory X)
  := make_algebraic_theory_morphism' _ (algebra_to_is_algebraic_theory_morphism' X).

Definition algebraic_theory_morphism_to_algebra_data
  {T : algebraic_theory}
  {X : hSet}
  (F : algebraic_theory_morphism T (set_endomorphism_theory X))
  : algebraic_theory_algebra_data T
  := make_algebraic_theory_algebra_data X F.

Lemma algebraic_theory_morphism_to_is_algebra
  {T : algebraic_theory}
  {X : hSet}
  (F : algebraic_theory_morphism T (set_endomorphism_theory X))
  : is_algebraic_theory_algebra (algebraic_theory_morphism_to_algebra_data F).
Proof.
  use make_is_algebraic_theory_algebra'.
  - do 5 intro.
    simpl.
    now rewrite (algebraic_theory_morphism_preserves_composition F).
  - do 3 intro.
    simpl.
    now rewrite (algebraic_theory_morphism_preserves_projections F).
Qed.

Definition algebraic_theory_morphism_to_algebra
  {T : algebraic_theory}
  {X : hSet}
  (F : algebraic_theory_morphism T (set_endomorphism_theory X))
  : algebraic_theory_algebra T
  := make_algebraic_theory_algebra _ (algebraic_theory_morphism_to_is_algebra F).

Lemma algebra_to_algebraic_theory_morphism_and_back
  {T : algebraic_theory}
  (A : algebraic_theory_algebra T)
  : algebraic_theory_morphism_to_algebra (algebra_to_algebraic_theory_morphism A) = A.
Proof.
  simpl.
  use algebraic_theory_algebra_eq.
  + apply idpath.
  + now intro.
Qed.

Lemma algebraic_theory_morphism_to_algebra_and_back
  {T : algebraic_theory}
  (y : ∑ X, algebraic_theory_morphism T (set_endomorphism_theory X))
  : pr1 y ,, algebra_to_algebraic_theory_morphism (algebraic_theory_morphism_to_algebra (pr2 y))
    = y.
Proof.
  use total2_paths2_f.
  + apply idpath.
  + rewrite idpath_transportf.
    apply algebraic_theory_morphism_eq.
    now do 2 intro.
Qed.

Definition algebra_weq_algebraic_theory_morphism
  {T : algebraic_theory}
  : algebraic_theory_algebra T ≃ ∑ X, algebraic_theory_morphism T (set_endomorphism_theory X)
  := weq_iso
    (λ (A : algebraic_theory_algebra T), (A : hSet) ,, algebra_to_algebraic_theory_morphism A)
    (λ X, algebraic_theory_morphism_to_algebra (pr2 X))
    algebra_to_algebraic_theory_morphism_and_back
    algebraic_theory_morphism_to_algebra_and_back. *)
