Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneMorphisms.
(* Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory. *)

Definition set_endomorphism_clone_data (X : hSet)
  : abstract_clone_data.
Proof.
  use make_abstract_clone_data.
  - use make_algebraic_base.
    + intro n.
      apply (make_hSet ((stn n → X) → X)).
      apply funspace_isaset.
      apply setproperty.
    + intros m n f g x.
      exact (f (λ i, g i x)).
  - intros n i x.
    exact (x i).
Defined.

Lemma set_endomorphism_is_clone (X : hSet)
  : is_abstract_clone (set_endomorphism_clone_data X).
Proof.
  use make_is_abstract_clone;
    now repeat intro.
Qed.

Definition set_endomorphism_clone (X : hSet)
  : abstract_clone
  := make_abstract_clone _ (set_endomorphism_is_clone X).

Definition algebra_to_abstract_clone_morphism_data
  {C : abstract_clone}
  (X : abstract_clone_algebra C)
  : abstract_clone_morphism_data C (set_endomorphism_clone X)
  := (λ _ f, action f).

Lemma algebra_to_is_abstract_clone_morphism
  {C : abstract_clone}
  (X : abstract_clone_algebra C)
  : is_abstract_clone_morphism (algebra_to_abstract_clone_morphism_data X).
Proof.
  use make_is_abstract_clone_morphism.
  - do 4 intro.
    apply funextfun.
    intro.
    apply abstract_clone_algebra_action_is_assoc.
  - intros n i.
    apply funextfun.
    intro.
    apply (abstract_clone_algebra_action_projects_component _ _ i).
Qed.

Definition algebra_to_abstract_clone_morphism
  {C : abstract_clone}
  (X : abstract_clone_algebra C)
  : abstract_clone_morphism C (set_endomorphism_clone X)
  := make_abstract_clone_morphism _ (algebra_to_is_abstract_clone_morphism X).

Definition abstract_clone_morphism_to_algebra_data
  {C : abstract_clone}
  {X : hSet}
  (F : abstract_clone_morphism C (set_endomorphism_clone X))
  : abstract_clone_algebra_data C
  := make_abstract_clone_algebra_data X F.

Lemma abstract_clone_morphism_to_is_algebra
  {C : abstract_clone}
  {X : hSet}
  (F : abstract_clone_morphism C (set_endomorphism_clone X))
  : is_abstract_clone_algebra (abstract_clone_morphism_to_algebra_data F).
Proof.
  use make_is_abstract_clone_algebra.
  - intros n i a.
    exact (maponpaths (λ f, f a) (abstract_clone_morphism_preserves_projections F _ _)).
  - intros m n f g a.
    exact (maponpaths (λ f, f a) (abstract_clone_morphism_preserves_composition F _ _ _ _)).
Qed.

Definition abstract_clone_morphism_to_algebra
  {C : abstract_clone}
  {X : hSet}
  (F : abstract_clone_morphism C (set_endomorphism_clone X))
  : abstract_clone_algebra C
  := make_abstract_clone_algebra _ (abstract_clone_morphism_to_is_algebra F).

Lemma algebra_to_abstract_clone_morphism_and_back
  {C : abstract_clone}
  (A : abstract_clone_algebra C)
  : abstract_clone_morphism_to_algebra (algebra_to_abstract_clone_morphism A) = A.
Proof.
  simpl.
  use abstract_clone_algebra_eq.
  + apply idpath.
  + now intro.
Qed.

Lemma abstract_clone_morphism_to_algebra_and_back
  {C : abstract_clone}
  (y : ∑ X, abstract_clone_morphism C (set_endomorphism_clone_data X))
  : pr1 y ,, algebra_to_abstract_clone_morphism (abstract_clone_morphism_to_algebra (pr2 y)) = y.
Proof.
  use total2_paths2_f.
  + apply idpath.
  + rewrite idpath_transportf.
    apply abstract_clone_morphism_eq.
    now do 2 intro.
Qed.

Definition algebra_weq_abstract_clone_morphism
  {C : abstract_clone}
  : abstract_clone_algebra C ≃ ∑ X, abstract_clone_morphism C (set_endomorphism_clone X)
  := weq_iso
    (λ (A : abstract_clone_algebra C), (A : hSet) ,, algebra_to_abstract_clone_morphism A)
    (λ X, abstract_clone_morphism_to_algebra (pr2 X))
    algebra_to_abstract_clone_morphism_and_back
    abstract_clone_morphism_to_algebra_and_back.
