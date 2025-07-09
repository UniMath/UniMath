(**************************************************************************************************

  The free object theory

  Given a forgetful functor from a category C into SET, and a corresponding free functor from SET to
  C, one can construct an algebraic theory T that has T(n) equal to the set (via the forgetful
  functor) of the free object on the set {1, ..., n}. Then every object of C can (using the
  forgetful functor again) be regarded as an algebra for this theory, and the construction of this
  algebra is functorial.

  Contents
  1. The free object theory [free_object_theory]
  2. The functor from objects of C to algebras for this theory [free_object_algebra_functor]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.

Local Open Scope cat.

Section FreeObjectTheory.

  Context {C : category}.
  Context {F : HSET ⟶ C}.
  Context {G : C ⟶ HSET}.
  Context {η : functor_identity HSET ⟹ F ∙ G}.
  Context {ϵ : G ∙ F ⟹ functor_identity C}.
  Context (H : form_adjunction F G η ϵ).

(** * 1. The free object theory *)

  Definition free_object_theory_data
    : algebraic_theory_data
    := make_algebraic_theory_data
      (λ n, G (F (stnset n)))
      (λ n, η (stnset n))
      (λ m n f g, #G (φ_adj_inv (make_adjunction _ H) (g : stnset m → _)) f).

  Definition free_object_is_theory
    : is_algebraic_theory free_object_theory_data.
  Proof.
    use make_is_algebraic_theory.
    - intros.
      refine (!eqtohomot (functor_comp G _ _) _ @ !_).
      apply (maponpaths (λ x, #G x f_l)).
      apply (φ_adj_inv_natural_postcomp (make_adjunction _ H)).
    - intros m n i f.
      refine (_ @ eqtohomot (pr2 H _) _).
      refine (eqtohomot (functor_comp G _ _) _ @ _).
      apply (maponpaths (#G _)).
      refine (!eqtohomot (nat_trans_ax η (stnset m) _ f) i).
    - intros n f.
      refine (maponpaths (λ x, _ x _) (pr1 H _) @ _).
      exact (eqtohomot (functor_id G _) _).
  Qed.

  Definition free_object_theory
    : algebraic_theory
    := make_algebraic_theory _ free_object_is_theory.

(** * 2. The functor from objects of C to algebras for this theory *)

  Section Algebra.

    Context (c : C).

    Definition free_object_algebra_data
      : algebra_data free_object_theory
      := make_algebra_data
        (G c)
        (λ n (f : free_object_theory n) a, #G (φ_adj_inv (make_adjunction _ H) (a : stnset n → _)) f).

    Lemma free_object_is_algebra
      : is_algebra free_object_algebra_data.
    Proof.
      use make_is_algebra.
      - intros m n f g a.
        refine (!eqtohomot (functor_comp G _ _) _ @ !_).
        apply (maponpaths (λ x, #G x f)).
        apply (φ_adj_inv_natural_postcomp (make_adjunction _ H)).
      - intros n i a.
        refine (_ @ eqtohomot (pr2 H _) _).
        refine (eqtohomot (functor_comp G _ _) _ @ _).
        apply (maponpaths (#G _)).
        refine (!eqtohomot (nat_trans_ax η (stnset n) _ a) i).
    Qed.

    Definition free_object_algebra
      : algebra free_object_theory
      := make_algebra _ free_object_is_algebra.

  End Algebra.

  Section AlgebraMorphism.

    Context (c c' : C).
    Context (f : c --> c').

    Definition free_object_algebra_morphism_data
      : free_object_algebra c → free_object_algebra c'
      := # G f.

    Lemma free_object_algebra_is_morphism
      (n : nat)
      (t : free_object_theory n)
      (a : stn n → free_object_algebra c)
      : mor_action_ax (identity free_object_theory) (free_object_algebra_morphism_data) (@action _ (free_object_algebra c)) (@action _ (free_object_algebra c')) n t a.
    Proof.
      refine (!eqtohomot (functor_comp G _ _) _ @ !_).
      apply (maponpaths (λ x, #G x t)).
      apply (φ_adj_inv_natural_postcomp (make_adjunction _ H)).
    Qed.

    Definition free_object_algebra_morphism
      : algebra_morphism (free_object_algebra c) (free_object_algebra c')
      := make_algebra_morphism _ free_object_algebra_is_morphism.

  End AlgebraMorphism.

  Definition free_object_algebra_functor_data
    : functor_data C (algebra_cat free_object_theory)
    := make_functor_data
        free_object_algebra
        free_object_algebra_morphism.

  Lemma free_object_algebra_is_functor
    : is_functor free_object_algebra_functor_data.
  Proof.
    split.
    - intro c.
      apply algebra_morphism_eq.
      apply (functor_id G).
    - intros c c' c'' f f'.
      apply algebra_morphism_eq.
      refine (_ @ !algebra_mor_comp _ _).
      exact (functor_comp G _ _).
  Qed.

  Definition free_object_algebra_functor
    : C ⟶ algebra_cat free_object_theory
    := make_functor _ free_object_algebra_is_functor.

End FreeObjectTheory.
