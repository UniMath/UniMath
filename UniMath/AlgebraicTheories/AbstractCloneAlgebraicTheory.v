Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.

(* The function from algebraic theories to abstract clones *)
Definition abstract_clone_data_from_algebraic_theory
  (T : algebraic_theory)
  : abstract_clone_data.
Proof.
  use make_abstract_clone_data.
  - exact T. 
  - intros.
    apply theory_pr.
    assumption.
Defined.

Lemma is_abstract_clone_from_algebraic_theory
  (T : algebraic_theory)
  : is_abstract_clone (abstract_clone_data_from_algebraic_theory T).
Proof.
  use make_is_abstract_clone. 
  - do 2 intro.
    apply AlgebraicTheories.comp_project_component.
  - apply algebraic_theory_comp_identity_projections.
  - apply algebraic_theory_comp_is_assoc.
Qed.

Definition abstract_clone_from_algebraic_theory
  (T : algebraic_theory)
  : abstract_clone
  := make_abstract_clone
    (abstract_clone_data_from_algebraic_theory T)
    (is_abstract_clone_from_algebraic_theory T).

(* The function from abstract clones to algebraic theories *)
Definition algebraic_theory_data_from_abstract_clone
  (C : abstract_clone)
  : algebraic_theory_data.
Proof.
  use make_algebraic_theory_data.
  - exact C.
  - exact (clone_pr firstelement).
  - exact (λ _ _ a f, reindex a f).
Defined.

Lemma is_algebraic_theory_from_abstract_clone
  (C : abstract_clone)
  : is_algebraic_theory (algebraic_theory_data_from_abstract_clone C).
Proof.
  use make_is_algebraic_theory.
  - split.
    + intro.
      apply funextfun.
      intro.
      apply abstract_clone_comp_identity_projections.
    + do 5 intro.
      apply funextfun.
      intro.
      simpl.
      unfold T_on_morphisms, compose.
      simpl.
      unfold reindex, funcomp.
      rewrite abstract_clone_comp_is_assoc.
      apply maponpaths, funextfun.
      intro.
      symmetry.
      apply abstract_clone_comp_project_component.
  - apply abstract_clone_comp_is_assoc.
  - do 2 intro.
    apply abstract_clone_comp_project_component.
  - do 2 intro.
    rewrite <- abstract_clone_comp_identity_projections.
    apply maponpaths, funextfun.
    intro.
    apply abstract_clone_comp_project_component.
  - do 6 intro.
    unfold T_on_morphisms, algebraic_theory_data_from_abstract_clone, reindex, AlgebraicBases.comp.
    simpl.
    rewrite (abstract_clone_comp_is_assoc C).
    apply maponpaths, funextfun.
    intro.
    apply abstract_clone_comp_project_component.
Qed.

Definition algebraic_theory_from_abstract_clone
  (C : abstract_clone)
  : algebraic_theory
  := make_algebraic_theory
    (algebraic_theory_data_from_abstract_clone C)
    (is_algebraic_theory_from_abstract_clone C).

(* Prove the weak equality *)
Local Lemma algebraic_theory_id 
  (T : algebraic_theory) : 
  algebraic_theory_from_abstract_clone (abstract_clone_from_algebraic_theory T) = T.
Proof.
  use algebraic_theory_eq.
  - apply idpath.
  - apply idpath.
  - rewrite idpath_transportf.
    unfold id_pr.
    simpl.
    unfold theory_pr.
    assert (H1 : (λ (_ : stn 1), firstelement) = identity (1 : finite_set_skeleton_category)).
    {
      apply funextfun.
      intro i.
      apply (subtypePairEquality (λ _, (isasetbool _ _))).
      exact (!(natlth1tois0 _ (stnlt i))).
    }
    rewrite H1.
    pose (H2 := pr1 (algebraic_theory_is_functor T)).
    unfold functor_idax in H2.
    simpl in H2.
    now rewrite H2.
  - rewrite idpath_transportf.
    do 4 (apply funextsec; intro).
    symmetry.
    apply functor_uses_projections.
Qed.

Local Lemma abstract_clone_id
  (C : abstract_clone)
  : abstract_clone_from_algebraic_theory (algebraic_theory_from_abstract_clone C) = C.
Proof.
  use abstract_clone_eq.
  - apply idpath.
  - now rewrite idpath_transportf.
  - rewrite idpath_transportf.
    do 2 (apply funextsec; intro).
    apply abstract_clone_comp_project_component.
Qed.

Lemma algebraic_theory_weq_abstract_clone : abstract_clone ≃ algebraic_theory.
Proof.
  use (algebraic_theory_from_abstract_clone ,, _).
  use isweq_iso.
  - exact abstract_clone_from_algebraic_theory.
  - exact abstract_clone_id.
  - exact algebraic_theory_id.
Defined.
