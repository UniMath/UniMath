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
Require Import UniMath.CategoryTheory.DaggerCategories.Isometry.
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

Section Dilators.
  Context (C : dagger_category).
  Local Notation "f †" := (C _ _ f).

  Definition dilation {x y : C} (f : x --> y) :=
    ∑ p : C, 
      ∑ (u : coisometry C p x) (v : coisometry C p y),
      u † · v = f.

  Definition dilation_map {x y : C} {f : x --> y} (d1 : dilation f) (d2 : dilation f) : UU.
  Proof.
    destruct d1 as (p & u1 & v1 & e1).
    destruct d2 as (q & u2 & v2 & e2).
    exact (∑ h : coisometry C p q, 
      (h · u2 = u1) × (h · v2 = v1)).
  Defined.

  Proposition dilation_map_eq {x y : C} {f : x --> y} {d e : dilation f} (h1 h2 : dilation_map d e)
    : pr1 h1 = pr1 h2 -> h1 = h2.
  Proof.
    intros p.
    use subtypePath.
    { intro. use isapropdirprod; use homset_property. }
    exact p.
  Qed.    

  Definition is_dilator {x y : C} {f : x --> y} (e : dilation f) : UU
    := ∏ d : dilation f, iscontr (dilation_map d e).

  Lemma isaprop_is_dilator {x y : C} {f : x --> y} {d : dilation f} 
    : isaprop (is_dilator d).
  Proof.
    apply impred.
    intro.
    apply isapropiscontr.
  Qed.

  Definition dilator {x y : C} (f : x --> y) : UU
    := ∑ d : dilation f, is_dilator d.

  Definition with_dilators : UU :=
    ∏ (x y : C) (f : x --> y), dilator f.

  Definition has_dilators : UU :=
    ∏ (x y : C) (f : x --> y), ∥dilator f∥.

  (* Example: dilation of the identity *)
  Definition dilation_id_id (x : C) : dilation (identity x).
  Proof.
    refine (x ,, coisometry_id C x ,, coisometry_id C x ,, _).
    cbn.
    rewrite dagger_to_law_id, id_left.
    reflexivity.
  Defined.

End Dilators.

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