(*********************************************
Dilators

In this file, we develop dagger-theoretic results about the category [prob_space C] of probability spaces.
The core results are that sample spaces (almost surely deterministic maps) can be identified with coisometries in 
the dagger-category [prob_space C], and that the relative product of probability spaces has the universal property of a dilator.

Table of Contents
1. Coisometries and Almost-Sure Determinism 

Todos:
2. Relative product and Dilators

References
- Noé Ensarguet and Paolo Perrone - 'Categorical probability spaces, ergodic decompositions, and transitions to equilibrium
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.Quotient.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.State.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.
Require Import UniMath.CategoryTheory.MarkovCategories.ProbabilitySpaces.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** 1. Coisometries and Almost-Sure Determinism  *)

Section DaggerLemmas.
  Context {C : markov_category_with_conditionals}.

  Proposition ase_determinism_coisometry {x y : C} (p : I_{C} --> x) (f : x --> y) :
       is_deterministic_ase p f 
    -> (bayesian_inverse p f) · f =_{p·f} identity y.
  Proof.
    intros det_ase.
    apply make_equal_almost_surely_r.
    
    etrans. {
      rewrite <- pairing_tensor_r.
      rewrite assoc.
      rewrite bayesian_inverse_eq_r.
      rewrite assoc'.
      rewrite pairing_tensor_r.
      rewrite id_left.
      reflexivity. }

    rewrite pairing_id.
    rewrite pairing_eq.
    rewrite assoc'.
    
    use ase_precomp.
    apply ase_symm.
    exact det_ase.
  Qed.    
  
End DaggerLemmas.

(* TODO Should be under /DaggerCategories *)
Section IsometriesCoisometries.
  (* TODO The definitions only require a dagger_structure! *)
  Context {C : category} (dag : dagger C).

  Notation "f †" := (dag _ _ f). (* TODO level etc *)

  Definition is_isometry {x y : C} (f : x --> y) : UU
    := f · (f †) = identity x.

  Definition is_coisometry {x y : C} (f : x --> y) : UU
    := (f †) · f = identity y.

  Proposition isometry_coisometry_dagger {x y : C} {f : x --> y} :
    is_isometry f <-> is_coisometry (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Proposition coisometry_isometry_dagger {x y : C} {f : x --> y} :
    is_coisometry f <-> is_isometry (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Proposition isometry_id {x : C} : is_isometry (identity x).
  Proof.
    unfold is_isometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Proposition coisometry_id {x : C} : is_coisometry (identity x).
  Proof.
    unfold is_coisometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Proposition isometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
    : is_isometry f -> is_isometry g -> is_isometry (f · g).
  Proof.
    unfold is_isometry. 
    intros isomf isomg.
    rewrite dagger_to_law_comp.
    assert(e : f · g · (g † · f †) = f · (g · g †) · f †). { rewrite !assoc. reflexivity. }
    rewrite e, isomg, id_right, isomf.
    reflexivity.
  Qed.

  Proposition coisometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
    : is_coisometry f -> is_coisometry g -> is_coisometry (f · g).
  Proof.
    intros coismf coisomg.
    apply coisometry_isometry_dagger.
    rewrite dagger_to_law_comp.
    apply isometry_comp ; apply coisometry_isometry_dagger; assumption.
  Qed.

  Proposition unitary_isometry_coisometry {x y : C} {f : x --> y} 
    : is_unitary dag f <-> (is_isometry f) × (is_coisometry f).
  Proof.
    unfold is_unitary, is_inverse_in_precat, is_isometry, is_coisometry.
    split; intros p; exact p.
  Qed. 

  Lemma z_iso_isometry_unitary {x y : C} (f : z_iso x y) 
    : is_isometry f -> is_unitary dag f.
  Proof.
    unfold is_isometry.
    intros isomf.
    pose (g := inv_from_z_iso f).
    assert (e : f † = g).
    { 
      rewrite <- (id_left (f †)).
      rewrite <- z_iso_after_z_iso_inv with f.
      rewrite <- assoc, isomf, id_right.
      reflexivity.     
    }
    split.
    - exact isomf.
    - rewrite e.
      apply z_iso_after_z_iso_inv.
  Qed.

  Lemma z_iso_coisometry_unitary {x y : C} (f : z_iso x y) 
    : is_coisometry f -> is_unitary dag f.
  Proof.
    unfold is_coisometry.
    intros coisomf.
    pose (g := inv_from_z_iso f).
    assert (e : f † = g).
    { 
      rewrite <- (id_right (f †)).
      rewrite <- z_iso_inv_after_z_iso with f.
      rewrite assoc, coisomf, id_left.
      reflexivity.     
    }
    split.
    - rewrite e.
      apply z_iso_inv_after_z_iso.
    - assumption.
  Qed.

End IsometriesCoisometries.

Section DaggerPropositions.
  Context {C : markov_category_with_conditionals}.

  Let C_is_causal : is_causal C := conditionals_imply_causality. 
  Let PS := prob_space (C_is_causal).

  Let dag : dagger PS := prob_space_dagger C.

  Lemma isos_coisometry {x y : PS} (f : z_iso x y) : is_coisometry dag f.
  Proof.
  Admitted.

  Proposition isos_unitary {x y : PS} (f : z_iso x y) : is_unitary dag f.
  Proof.
    apply z_iso_coisometry_unitary.
    apply isos_coisometry.
  Qed.

End DaggerPropositions.