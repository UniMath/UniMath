(*********************************************
Probability Spaces

We define the categories of probability spaces over a causal Markov category C.
- the objects are states (X,p) (i.e. objects equipped with a probability distribution)
  * this is definitionally the same as the type [state C] of `State.v`
  * it is also definitionally the same as the type of objects of the slice category I/C
- morphisms f : (X,p) --> (Y,q) are p-almost sure equivalence classes of morphisms f : X --> Y
  which preserve the state (i.e. p · f = q)

To construct this category, we use the quotient construction [mor_quot_category] of
the slice category I/C under the congruence relation given by almost-sure equality.

Table of Contents
1. Definition of the Category of Probability Spaces
2. Definition of the Dagger Structure on Probability Spaces, given by Bayesian Inversion

The following future work needs to be added to this file: 
* Proof that probability spaces are equivalent as a dagger category to the category of couplings from Couplings.v
* Think about univalence of the probability space construction

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
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

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** 1. Definition of the Category of Probability Spaces *)

Section ProbabilitySpaces.
  Context {C : markov_category}
          (causality : is_causal C).
  
  Definition states_cat : category.
  Proof.
    use coslice_cat.
    + exact C.
    + exact I_{C}.
  Defined.

  (**
  In the next definition we use that states are definitionally the same as objects of states_cat.
  If that was not the case, that definition would not type check.
  *)

  Definition state_mor (p q : state C) : UU := states_cat ⟦ p, q ⟧ .

  Coercion state_mor_to_mor {p q : state C} (f : state_mor p q)
    : C ⟦ state_ob p , state_ob q ⟧ := pr1 f.

  Proposition state_mor_eq {p q : state C} (f : state_mor p q) : p · f = q.
  Proof.
    exact (pr2 f).
  Qed.

  Definition ase_states (p q : state C) : hrel (state_mor p q).
  Proof. 
    intros f g.
    use make_hProp.
    - exact (f =_{p} g).
    - apply isaprop_ase.
   Defined.

  Proposition is_eqrel_ase_states (p q : state C) : iseqrel (ase_states p q).
  Proof.
    repeat split.
    - intros f g h.
      apply ase_trans.
    - intros f g.
      apply ase_symm.
  Qed.

  Proposition ase_states_cong
              {p q r : state C}
              {f f' : state_mor p q}
              {g g' : state_mor q r}
              (e₁ : ase_states _ _ f f')
              (e₂ : ase_states _ _ g g')
    : ase_states _ _ (f · g) (f' · g').
  Proof.
    use ase_congruence.
    - exact causality.
    - exact q.
    - exact e₁.
    - exact e₂.
    - exact (!(state_mor_eq f)).
  Qed.

  Definition ase_cong : mor_cong_rel states_cat.
  Proof.
    use make_mor_cong_rel.
    - intros p q.
      use make_eqrel.
      + apply ase_states.
      + apply is_eqrel_ase_states.
    - intros p q r f f' g g'. 
      cbn.
      apply ase_states_cong.
  Defined.   
    
  Definition prob_space : category.
  Proof.
    use mor_quot_category.
    - exact states_cat.
    - exact ase_cong.
  Defined.

End ProbabilitySpaces.

(** 2. Definition of the Dagger Structure on Probability Spaces, given by Bayesian Inversion *)

Section ProbabilitySpacesDagger.
  Context (C : markov_category_with_conditionals).
  
  Let C_is_causal : is_causal C := conditionals_imply_causality.

  Definition prob_space_dagger_structure : dagger_structure (prob_space C_is_causal).
  Proof.
    intros [x p] [y q].
    use setquotfun.
    - (* Use [bayesian_inverse] as the dagger *)
      intros [f e].
      simple refine (bayesian_inverse p f ,, _).
      + abstract (rewrite <- e; apply bayesian_inverse_state_preservation).   
 
    - (* bayesian inverse is compatible with almost sure equality *)
      intros [f fpres] [g gpres].
      intros e.
      cbn. cbn in *.
      use bayesian_inverse_ase_unique'.
      + exact p. 
      + exact f.
      + assumption.
      + apply bayesian_inverse_eq.
      + use is_bayesian_inverse_ase_cong.
        * exact g.  
        * exact (bayesian_inverse p g).
        * apply ase_symm; assumption.
        * apply ase_refl.
        * apply bayesian_inverse_eq.    
  Defined.

  Definition prob_space_dagger_laws : dagger_laws prob_space_dagger_structure.
  Proof.
    repeat split.
    - (* Identity *)
      intros [x p].
      apply iscompsetquotpr.
      use bayesian_inverse_ase_unique'.
      + exact p.
      + exact (identity x).
      + rewrite id_right. reflexivity.
      + apply bayesian_inverse_eq.
      + apply bayesian_inverse_identity. 

    - (* Composition *)
      intros [x p] [y q] [z r].
      use setquotunivprop'.
      { 
        intro.
        use impred. (* TODO this line is very slow *)
        intro.
        apply homset_property.
      }
      intros [f e]. 
      use setquotunivprop'. { intro. apply homset_property. }   
      intros [g h].
      apply iscompsetquotpr.
      cbn. cbn in *.
      use bayesian_inverse_ase_unique'.
      + exact p.
      + exact (f · g).
      + rewrite assoc, e, h. reflexivity.
      + apply bayesian_inverse_eq.
      + apply bayesian_inverse_comp.
        * apply bayesian_inverse_eq.
        * rewrite e; apply bayesian_inverse_eq.
                
    - (* Idempotence *) 
      intros [x p] [y q].
      use setquotunivprop'. { intro ; apply homset_property. }
      intros [f e].
      apply iscompsetquotpr.
      cbn. cbn in e.
      rewrite <- e.
      use bayesian_inverse_ase_unique'.
      + exact (p · f).
      + exact (bayesian_inverse p f).
      + apply bayesian_inverse_state_preservation.
      + apply bayesian_inverse_eq.
      + apply bayesian_inverse_idempotent.
        apply bayesian_inverse_eq. 
  Defined.

  Definition prob_space_dagger : dagger (prob_space C_is_causal)
    := _ ,, prob_space_dagger_laws.

End ProbabilitySpacesDagger.

Section ProbabilitySpacesToCouplings.
  Context {C : markov_category_with_conditionals}.

  Let C_is_causal : is_causal C := conditionals_imply_causality. 
  Let PS := prob_space (C_is_causal).

  Let dag : dagger PS := prob_space_dagger C.

  (* Extract the bloom couplings from a PS-morphism *)
  Definition ps_bloom {p q : PS} (f : p --> q) : homset I_{C} ((pr1 p) ⊗ (pr1 q)).
  Proof.
    destruct p as [x p].
    destruct q as [y q].
    revert f.
    use setquotuniv.
    { 
      intros [f e].
      apply (bloom_coupling p f). 
    }
    abstract (intros [f e] [g h] ase; apply equal_almost_surely_r; exact ase).
  Defined.

  Proposition ps_bloom_dom {p q : PS} {f : p --> q} : ps_bloom f · proj1 = pr2 p.
  Proof.
    unfold ps_bloom.
    revert f.
    apply setquotunivprop'. { intros. apply homset_property. } 
    intros [f e].
    cbn.
    apply bloom_coupling_dom.
  Qed.

  Proposition ps_bloom_cod {p q : PS} {f : p --> q} : ps_bloom f · proj2 = pr2 q.
  Proof.
    unfold ps_bloom.
    revert f.
    apply setquotunivprop'. { intros. apply homset_property. } 
    intros [f e].
    cbn in *.
    rewrite <- e.
    apply bloom_coupling_cod.
  Qed.  
  
  Definition ps_to_coupling {p q : PS} (f : p --> q) : coupling (pr2 p) (pr2 q).
  Proof.
    use make_coupling.
    - exact (ps_bloom f).
    - apply ps_bloom_dom.
    - apply ps_bloom_cod.
  Defined.  

  Definition ps_to_couplings_data : functor_data PS (couplings C).
  Proof.
    use make_functor_data.
    - exact (λ p, p).
    - intros [x p] [y q] f.
      exact (ps_to_coupling f).
  Defined.  

  (* The functor from probability spaces to couplings *)
  Definition ps_to_couplings : functor PS (couplings C).
  Proof.
    use make_functor. { exact ps_to_couplings_data. }
    split.
    - (* Identity law *)
      intros [x p].
      apply coupling_ext.
      apply bloom_coupling_id.
      
    - (* Composition law *)
      intros [x p] [y q] [z r].
      use setquotunivprop'. { intro. use impred. intro. apply homset_property. }
      intros [f e].
      use setquotunivprop'. { intro. apply homset_property. }
      intros [g h].
      apply coupling_ext.
      cbn in *.
      rewrite <- e.
      symmetry.
      apply bloom_coupling_composition.
  Defined.

End ProbabilitySpacesToCouplings.

Section CouplingsToProbabilitySpaces.
  Context {C : markov_category_with_conditionals}.

  Let C_is_causal : is_causal C := conditionals_imply_causality. 
  Let PS := prob_space (C_is_causal).

  Let dag : dagger PS := prob_space_dagger C.

  Definition coupling_cond {p q : couplings C} (γ : p --> q) : (pr1 p) --> (pr1 q)
    := ((coupling_to_state γ) |1).

  Lemma coupling_cond_state_preservation {p q : couplings C} (γ : p --> q) 
    : (pr2 p) · (coupling_cond γ) = (pr2 q).
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [dom cod]].
    unfold coupling_cond.
    cbn in *.
    assert(E : p · γ |1 = (γ · proj1) · ⟨identity _, γ |1⟩ · proj2).
    { 
      rewrite dom. 
      rewrite <- assoc.
      rewrite pairing_proj2.
      reflexivity. 
    }  
    rewrite E.
    rewrite <- conditional_distribution_1_eq.
    exact cod.
  Qed.
    
  Definition coupling_to_ps {p q : couplings C} (γ : p --> q) : PS ⟦ p,  q ⟧.
  Proof.
    apply setquotpr.
    exists (coupling_cond γ).
    apply coupling_cond_state_preservation.
  Defined.

  Definition couplings_to_ps_data : functor_data (couplings C) PS.
  Proof.
    use make_functor_data.
    - exact (λ p, p).
    - intros [x p] [y q] γ.
      exact (coupling_to_ps γ).
  Defined.
  
  Definition couplings_to_ps : functor (couplings C) PS.
  Proof.
    use make_functor. { exact couplings_to_ps_data. }
    split.
    - (* Identitiy law *)
      intros [x p].
      apply iscompsetquotpr.
      unfold coupling_cond.
      cbn.
      apply ase_symm.
      use conditional_distribution_1_ase_unique'. { apply identity_coupling_dom. }
      unfold identity_coupling.
      rewrite pairing_id.
      reflexivity.
    
    - (* Composition law *)
      intros [x p] [y q] [z r] [β [domβ codβ]] [γ [domγ codγ]].
      apply iscompsetquotpr.
      unfold coupling_cond.
      cbn in *.
      assert(compat : β · proj2 = γ · proj1). { rewrite codβ, domγ. reflexivity. }
      apply ase_symm.
      use conditional_distribution_1_ase_unique'. {
        rewrite coupling_composition_dom; assumption.
      }
      rewrite <- domβ.
      apply coupling_composition_eq_4; assumption.
  Qed.      

End CouplingsToProbabilitySpaces.