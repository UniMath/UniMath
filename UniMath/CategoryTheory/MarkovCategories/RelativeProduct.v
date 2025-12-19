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

  (* Here is the central lemma for dilators *)

(*   Proposition dilator_existence {w x y : C} {r p q} (c : x --> y) (p c = q)
    (f : w --> x) (g : w --> y)  *)
  


End Dilators.

Section CouplingDilators.
  Context {C : markov_category_with_conditionals}.
  Let krn := couplings_dagger_cat C.

  (* Dagger couplings*)

  Definition dilation_coupling {r x y : C} (p : I_{C} --> r) 
    (f : r --> x) (g : r --> y) : I_{C} --> x ⊗ y := p · ⟨f, g⟩.

  Proposition dilation_coupling_dom
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : dilation_coupling p f g · proj1 = p · f.
  Proof.
    unfold dilation_coupling. 
    rewrite assoc', pairing_proj1.
    reflexivity.
  Qed.

  Proposition dilation_coupling_cod
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : dilation_coupling p f g · proj2 = p · g.
  Proof.
    unfold dilation_coupling. 
    rewrite assoc', pairing_proj2.
    reflexivity.
  Qed.

  Proposition dilation_coupling_dagger
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : coupling_dagger (dilation_coupling p f g) = dilation_coupling p g f.
  Proof.
    unfold dilation_coupling, coupling_dagger.
    rewrite assoc', pairing_sym_mon_braiding.
    reflexivity.
  Qed.

  Proposition dilation_coupling_identity {r : C} (p : I_{C} --> r) :
    dilation_coupling p (identity r) (identity r) = identity_coupling p.
  Proof.
    unfold dilation_coupling, identity_coupling.
    rewrite pairing_id.
    reflexivity.
  Qed.

  Proposition dilation_coupling_inv_l 
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : dilation_coupling p f g = dilation_coupling (p · f) (identity x) (bayesian_inverse p f · g).
  Proof.
    unfold dilation_coupling.
    rewrite <- pairing_tensor_r, assoc.
    rewrite bayesian_inverse_eq_r.
    rewrite assoc', pairing_tensor_r, id_left.
    reflexivity.
  Qed.

  Proposition dilation_coupling_inv_r
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : dilation_coupling p f g = dilation_coupling (p · g) (bayesian_inverse p g · f) (identity y).
  Proof.
    unfold dilation_coupling.
    rewrite <- pairing_tensor_l, assoc.
    rewrite bayesian_inverse_eq_l.
    rewrite assoc', pairing_tensor_l, id_left.
    reflexivity.
  Qed.

  Proposition bloom_dilation_composition 
    {r x y : C} (p : I_{C} --> r) (f : r --> x) (g : r --> y)
    : coupling_composition (coupling_dagger (bloom_coupling p f)) (bloom_coupling p g) = dilation_coupling p f g.
  Proof.
    unfold coupling_dagger.
    rewrite coupling_composition_eq_2.
    2: { rewrite assoc'.
         rewrite sym_mon_braiding_proj2.
         rewrite !bloom_coupling_dom.
         reflexivity. }
    etrans. {
      assert(e : bloom_coupling p f = p · ⟨ identity _, f ⟩). { reflexivity. }
      rewrite e.
      rewrite !assoc'.
      apply maponpaths.
      rewrite assoc, pairing_sym_mon_braiding.
      rewrite <- pairing_split_r.
      reflexivity.
    }
    unfold dilation_coupling.
    apply ase_precomp.
    apply ase_pairing_r.
    apply bloom_coupling_conditional_1_ase.
  Qed.   
     

 (*  Proposition dilation_coupling_as_det  *)

  (* Dilator coupling *)
(*   Proposition dilator_coupling (gamma : I_{C} --> x ⊗ y)  *)

  (* .......... *)

  Definition bloomc {x y : C} (p : I_{C} --> x) (f : x --> y) : 
      krn ⟦ (x ,, p) , (y,, p · f) ⟧. (* coupling p (p cdot f) *)
  Proof.
    use make_coupling.
    - exact (bloom_coupling p f).
    - apply bloom_coupling_dom.
    - apply bloom_coupling_cod.
  Defined.  

(*   Definition bloom_ex_t {x y : C} {p q : krn} (f : C ⟦ x , y ⟧) 
    (dom : state_ob p = x) (cod : state_ob q = y) : UU.
  Proof.
    rewrite <- dom, <- cod in f.
    refine (∏ (pres : (pr2 p) · f = (pr2 q)), krn ⟦ p, q ⟧).
  Defined.

  Proposition bloom_ex {x y : C} {p q : krn} (f : C ⟦ x , y ⟧) 
    (dom : state_ob p = x) (cod : state_ob q = y)  : bloom_ex_t f dom cod.
  Proof.
    intros pres.
    use make_coupling.
    - exact (bloom_coupling (pr2 p) f).  *)


  Definition dilationc {r x y : C} (p : I_{C} --> r) 
    (f : r --> x) (g : r --> y) : krn ⟦ (x ,, p · f) , (y,, p · g) ⟧.
  Proof.
    use make_coupling.
    - exact (dilation_coupling p f g).
    - apply dilation_coupling_dom.
    - apply dilation_coupling_cod.
  Defined.

  Proposition bloom_dilation {x y z : C} (p : I_{C} --> x) (f : x --> y) (g : x --> z) :
    {bloomc p f}_krn^† · (bloomc p g) = dilationc p f g.
  Proof.
    apply coupling_ext.
    cbn.
    apply bloom_dilation_composition.
  Qed.

  Proposition bloom_coupling_coiso {x y : C} {p : I_{C} --> x} (f : x --> y) :
    is_deterministic_ase p f -> is_coisometry krn (bloomc p f).
  Proof.
    intros det_ase.
    apply coupling_ext.
    rewrite bloom_dilation.
    cbn.
    unfold dilation_coupling, identity_coupling.
    rewrite pairing_eq, assoc'.
    apply ase_precomp.
    apply ase_symm.
    exact det_ase.
  Qed.

  Definition bloom_coupling_to_coiso {x y : C} {p : I_{C} --> x} (f : x --> y) :
    is_deterministic_ase p f -> coisometry krn (x ,, p) (y ,, p · f).
  Proof.
    intros det_ase.
    use make_coisometry.
    - exact (bloomc p f).
    - abstract (apply bloom_coupling_coiso; assumption).
  Defined.

  Definition relprod {p q : krn} (γ : p --> q) : krn.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    exact (x ⊗ y ,, γ).
  Defined.

  Definition pi1 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) p.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    cbn in *.
    rewrite <- domγ.
    apply bloom_coupling_to_coiso.
    apply deterministic_implies_determinstic_ase.
    apply is_deterministic_proj1.
  Defined.

  Definition p1 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) p.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    use make_coisometry.
    - use make_coupling.
      * refine (bloom_coupling γ proj1).
      * apply bloom_coupling_dom.
      * abstract (cbn in *; rewrite <- domγ; apply bloom_coupling_cod).
    - apply coupling_ext.
      cbn.
      rewrite bloom_dilation_composition.
      unfold dilation_coupling, identity_coupling.
      rewrite pairing_eq.
      cbn in domγ.
      rewrite <- domγ.
      rewrite assoc'.
      apply ase_precomp.
      apply ase_symm.
      apply deterministic_implies_determinstic_ase.
      apply is_deterministic_proj1.
  Defined.

  Definition pi2 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) q.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    cbn in *.
    rewrite <- codγ.
    apply bloom_coupling_to_coiso.
    apply deterministic_implies_determinstic_ase.
    apply is_deterministic_proj2.
  Defined.

  Definition p2 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) q.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    use make_coisometry.
    - use make_coupling.
      * refine (bloom_coupling γ proj2).
      * apply bloom_coupling_dom.
      * abstract (cbn in *; rewrite <- codγ; apply bloom_coupling_cod).
    - apply coupling_ext.
      cbn.
      rewrite bloom_dilation_composition.
      unfold dilation_coupling, identity_coupling.
      rewrite pairing_eq.
      cbn in codγ.
      rewrite <- codγ.
      rewrite assoc'.
      apply ase_precomp.
      apply ase_symm.
      apply deterministic_implies_determinstic_ase.
      apply is_deterministic_proj2.
  Defined.

  Proposition dilator_dilation {p q : krn} (γ : p --> q) :
    {p1 γ}_krn^† · (p2 γ) = γ.
  Proof.
    apply coupling_ext.
    unfold p1, p2.
    cbn.
    rewrite bloom_dilation_composition.
    unfold dilation_coupling.
    rewrite pairing_proj_id, id_right.
    reflexivity.
  Qed.

  Definition coupling_dilator {p q : krn} (γ : p --> q) : dilation krn γ.
  Proof.
    destruct p as [x p], q as [y q].
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (relprod γ).
    - apply p1.
    - apply p2.
    - apply dilator_dilation. 
  Defined.

  Proposition coupling_dilator_factorization {p q : krn} (γ : p --> q) (d : dilation krn γ)
    : dilation_map krn d (coupling_dilator γ).
  Proof.
    pose(f := (coupling_to_state (coisometry_to_mor (left d)))|1).
    pose(g := (coupling_to_state (coisometry_to_mor (right d)))|1).
    pose(w := apex d).
    use make_dilation_map. {
      unfold apex. cbn.
      use make_coupling.
      - use bloom_coupling.
  Abort.

  Proposition coupling_dilator_is_dilator {p q : krn} (γ : p --> q) : 
    is_dilator krn (coupling_dilator γ).
  Proof.
  Abort.


End CouplingDilators.