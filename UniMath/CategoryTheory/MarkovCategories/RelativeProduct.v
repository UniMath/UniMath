(*********************************************
Relative Product

In this file, we develop dagger-categorical results about the category [prob_space C] of probability spaces.

The core results are 
* almost surely deterministic maps can be identified with coisometries in [prob_space]
* the relative product construction on probability spaces has the universal property of a dilator

Table of Contents
1. Coisometries and Almost-Sure Determinism 
2. Relative product and Dilators

References
- Noé Ensarguet and Paolo Perrone - 'Categorical probability spaces, ergodic decompositions, and transitions to equilibrium'
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
Require Import UniMath.CategoryTheory.MarkovCategories.RelativePositivity.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.
Require Import UniMath.CategoryTheory.MarkovCategories.Couplings.
Require Import UniMath.CategoryTheory.MarkovCategories.ProbabilitySpaces.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Isometry.
Require Import UniMath.CategoryTheory.DaggerCategories.Dilators.
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
      rewrite <- pairing_tensor_r, assoc.
      rewrite bayesian_inverse_eq_r, assoc'.
      rewrite pairing_tensor_r, id_left.
      reflexivity. }

    rewrite pairing_id.
    rewrite pairing_eq.
    rewrite assoc'.
    
    use ase_precomp.
    apply ase_symm.
    exact det_ase.
  Qed.

  Proposition coisometry_ase_deterministic {x y : C} (p : I_{C} --> x) (f : x --> y) :
    (bayesian_inverse p f) · f =_{p·f} identity y -> is_deterministic_ase p f.
  Proof.
    intros e.
    use relpos_coisometry_lemma.
    - apply conditionals_imply_relative_positivity.
    - exact (bayesian_inverse p f).
    - apply bayesian_inverse_eq.
    - exact e.
  Qed.

End DaggerLemmas.

Section DaggerPropositions.
  Context {C : markov_category_with_conditionals}.

  Let C_is_causal : is_causal C := conditionals_imply_causality. 
  Let PS := prob_space (C_is_causal).

  Let dag : dagger PS := prob_space_dagger C.

  Local Lemma isos_coisometry_aux {x y : PS} :
    ∏ (ff : x --> y) (gg : y --> x)
    (inv_ffgg : ff · gg = identity _) (inv_ggff : gg · ff = identity _), is_coisometry dag ff.
  Proof.
    destruct x as [x p], y as [y q].

    use setquotunivprop'. { do 3 (intro; use impred). intro. apply homset_property. }
    intros [f presf].  
    use setquotunivprop'. { do 2 (intro; use impred). intro. apply homset_property. }
    intros [g presg] inv_fg inv_gf.
    apply iscompsetquotpr.
    cbn. 
    pose(ase_fg := setquotpreq _ _ _ inv_fg).
    cbn in ase_fg.

    do 2 cbn in presf.
    rewrite <- presf.
    apply ase_determinism_coisometry.
    use relpos_coisometry_lemma.
    - apply conditionals_imply_relative_positivity.
    - exact g.
    - apply splitting_to_bayesian_inverse.
      * apply conditionals_imply_relative_positivity.
      * exact ase_fg.
    - pose(ase_gf := setquotpreq _ _ _ inv_gf).
      cbn in ase_gf.
      rewrite presf.
      exact ase_gf.
  Qed.

  Proposition isos_coisometry {x y : PS} (phi : z_iso x y) : is_coisometry dag phi.
  Proof.
    use isos_coisometry_aux.
    - apply z_iso_inv.
      exact phi.
    - apply z_iso_inv_after_z_iso.
    - apply z_iso_after_z_iso_inv.
  Qed.  

  Proposition isos_unitary {x y : PS} (f : z_iso x y) : is_unitary dag f.
  Proof.
    apply z_iso_coisometry_unitary.
    apply isos_coisometry.
  Qed.

End DaggerPropositions.

(** * 2. Relative product and Dilators *)

Section Dilators.
  Context {C : markov_category_with_conditionals}.
  Let PS := prob_space_dagger_cat C.

  Definition hProj {X : UU} (i : isaset X) (x : make_hSet X i) : X.
  Proof.
    exact x.
  Defined.

  Definition bloom_space {p q : PS} (f : p --> q) : PS.
  Proof.
    destruct p as [x p], q as [y q].
    refine (x ⊗ y ,, _).
    use hProj. { apply homset_property. } 
    revert f.
    use setquotuniv.
    - intros [f e].
      exact (bloom_coupling p f).
    - intros [f e] [g h] ase.
      unfold bloom_coupling.
      apply equal_almost_surely_r.
      exact ase.
  Defined.

  Definition bloom_space_proj1 {p q : PS} (f : p --> q) : (bloom_space f) --> p.
  Proof.
    use hProj. { apply homset_property. } 
    revert f.
  Abort.
    
  Proposition isaset_dilation {x y : PS} (f : x --> y) : isaset (dilation PS f).
  Proof.
    apply (isofhleveltotal2 2).
  Abort.
    

  Definition bloom_dilation {p q : PS} (f : p --> q) : dilation PS f.
  Proof.
  Abort. (*
    destruct p as [x p], q as [y q].
    use hProj. {  } 
    revert f.
    use setquotuniv.
     
  Defined.*)
  


End Dilators.

Section CouplingDilators.
  Context {C : markov_category_with_conditionals}.
  Let krn := couplings_dagger_cat C.

  Definition det_to_coisom {x y : C} {p : I_{C} --> x} (f : x --> y): 
    is_deterministic_ase p f -> coisometry krn (x ,, p) (y,, p · f).
  Proof.
    intros detf.
    use make_coisometry.
    - use make_coupling.
      + apply (bloom_coupling p f).
      + apply bloom_coupling_dom.
      + apply bloom_coupling_cod.
    - unfold is_coisometry.
      unfold bloom_coupling.
      apply coupling_ext.
      cbn.
      unfold coupling_dagger, identity_coupling.
      rewrite <- assoc.
      rewrite pairing_sym_mon_braiding.
      rewrite coupling_composition_eq_2.
  Abort.

        

  Definition coupling_dilation {p q : krn} (γ : p --> q): dilation krn γ.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (x ⊗ y ,, γ).
  - Abort.
    


End CouplingDilators.