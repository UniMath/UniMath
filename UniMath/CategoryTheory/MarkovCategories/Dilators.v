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

Section IsometriesDef.
  Context {C : category} (dag : dagger_structure C).
  Local Notation "f †" := (dag _ _ f).

  Definition is_isometry {x y : C} (f : x --> y) : UU
  := f · (f †) = identity x.

  Definition isometry (x y : C) : UU
  := ∑ f : x --> y, is_isometry f.

  Definition make_isometry {x y : C} (f : x --> y) (p : is_isometry f) : isometry x y
    := f ,, p.

  Coercion isometry_to_mor {x y : C} (f : isometry x y) : x --> y 
    := pr1 f.

  Proposition isometry_property {x y : C} (f : isometry x y) : is_isometry f.
  Proof.
    exact (pr2 f).
  Qed. 

  Lemma isaprop_is_isometry {x y : C} (f : x --> y) 
    : isaprop (is_isometry f).
  Proof.
    apply homset_property.
  Qed.

  Lemma isaset_isometry {x y : C} : isaset (isometry x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_isometry.
  Qed.

  Lemma isometry_eq {x y : C} (f g : isometry x y) :
    pr1 f = pr1 g -> f = g.
  Proof.
    intro p.
    apply (total2_paths_f p).
    apply isaprop_is_isometry.
  Qed.

End IsometriesDef.

Section CoisometriesDef.
  Context {C : category} (dag : dagger_structure C).
  Local Notation "f †" := (dag _ _ f).

  Definition is_coisometry {x y : C} (f : x --> y) : UU
    := (f †) · f = identity y.

  Definition coisometry (x y : C) : UU
  := ∑ f : x --> y, is_coisometry f.

  Definition make_coisometry {x y : C} (f : x --> y) (p : is_coisometry f) : coisometry x y
    := f ,, p.

  Coercion coisometry_to_mor {x y : C} (f : coisometry x y) : x --> y 
    := pr1 f.

  Proposition coisometry_property {x y : C} (f : coisometry x y) : is_coisometry f.
  Proof.
    exact (pr2 f).
  Qed. 

  Lemma isaprop_is_coisometry {x y : C} (f : x --> y) 
    : isaprop (is_coisometry f).
  Proof.
    apply homset_property.
  Qed.

  Lemma isaset_coisometry {x y : C} : isaset (coisometry x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_coisometry.
  Qed.

  Lemma coisometry_eq {x y : C} (f g : coisometry x y) :
    pr1 f = pr1 g -> f = g.
  Proof.
    intro p.
    apply (total2_paths_f p).
    apply isaprop_is_coisometry.
  Qed.

End CoisometriesDef.

Section IsometryCoisometryProperties.
  Context {C : category} (dag : dagger C).
  Local Notation "f †" := (dag _ _ f).

  (* Isometries: Identity and composition *)
  Proposition is_isometry_id {x : C} : is_isometry dag (identity x).
  Proof.
    unfold is_isometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Definition isometry_id (x : C) : isometry dag x x.
  Proof.
    use make_isometry.
    - exact (identity x).
    - apply is_isometry_id.
  Defined.

  Proposition is_isometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
  : is_isometry dag f -> is_isometry dag g -> is_isometry dag (f · g).
  Proof.
    unfold is_isometry. 
    intros isomf isomg.
    rewrite dagger_to_law_comp.
    assert(e : f · g · (g † · f †) = f · (g · g †) · f †). { rewrite !assoc. reflexivity. }
    rewrite e, isomg, id_right, isomf.
    reflexivity.
  Qed.

  Definition isometry_comp {x y z : C} (f : isometry dag x y) (g : isometry dag y z) 
    : isometry dag x z.
  Proof.
    use make_isometry.
    - exact (f · g).
    - apply is_isometry_comp; apply isometry_property.
  Defined.

  (* Coisometries: Identity and composition *)
  Proposition is_coisometry_id {x : C} : is_coisometry dag (identity x).
  Proof.
    unfold is_coisometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Definition coisometry_id (x : C) : coisometry dag x x.
  Proof.
    use make_coisometry.
    - exact (identity x).
    - apply is_coisometry_id.
  Defined.

  Proposition is_coisometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
  : is_coisometry dag f -> is_coisometry dag g -> is_coisometry dag (f · g).
  Proof.
    unfold is_coisometry. 
    intros coisomf coisomg.
    rewrite dagger_to_law_comp.
    assert(e : g † · f † · (f · g) = g † · (f † · f) · g). { rewrite !assoc. reflexivity. }
    rewrite e, coisomf, id_right, coisomg.
    reflexivity.
  Qed.

  Definition coisometry_comp {x y z : C} (f : coisometry dag x y) (g : coisometry dag y z)
    : coisometry dag x z.
  Proof.
    use make_coisometry.
    - exact (f · g).
    - apply is_coisometry_comp; apply coisometry_property.
  Defined.

  (* Dagger lemmas *)

  Proposition isometry_coisometry_dagger {x y : C} {f : x --> y}
    : is_isometry dag f <-> is_coisometry dag (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Proposition coisometry_isometry_dagger {x y : C} {f : x --> y}
    : is_coisometry dag f <-> is_isometry dag (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Definition isometry_dag {x y : C} (f : isometry dag x y) : coisometry dag y x.
  Proof.
    use make_coisometry.
    - exact (f †).
    - abstract (apply isometry_coisometry_dagger; apply isometry_property).
    Defined.  

  Definition coisometry_dag {x y : C} (f : coisometry dag x y) : isometry dag y x.
  Proof.
    use make_isometry.
    - exact (f †).
    - abstract (apply coisometry_isometry_dagger; apply coisometry_property).
  Defined. 

  (* Relation with unitaries *)

  Proposition unitary_isometry_coisometry {x y : C} {f : x --> y} 
    : is_unitary dag f <-> (is_isometry dag f) × (is_coisometry dag f).
  Proof.
    unfold is_unitary, is_inverse_in_precat, is_isometry, is_coisometry.
    split; intros p; exact p.
  Qed.
  
  Definition unitary_to_isometry {x y : C} (f : unitary dag x y) : isometry dag x y.
  Proof.
    use make_isometry.
    - exact f.
    - abstract (apply unitary_isometry_coisometry; exact (pr2 f)).
  Defined.  

  Lemma z_iso_isometry_unitary {x y : C} (f : z_iso x y) 
    : is_isometry dag f -> is_unitary dag f.
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
    : is_coisometry dag f -> is_unitary dag f.
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

  (* Cancellation stuff *)

  (* TODO: isometries are mono, coisometries epi *)

End IsometryCoisometryProperties.

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