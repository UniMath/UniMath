(*********************************************
Conditionals.InformationFlow

We prove various information flow axioms and reasoning principles that are derivable from
the existence of conditionals.

1. Conditionals Imply Causality
  - Every Markov category with conditionals is causal, hence
    relatively positive, positive, and all isomorphisms are deterministic
2. Relative Positivity
  - relative positivity allows some useful characterizations related to Bayesian inversion
    and the category of probability spaces

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.Definition.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** 1. Conditionals Imply Causality *)

Section ConditionalsImplyCausalityLemmas.
  Context {C : markov_category_with_conditionals}.
  Context {x y z : C}.
  Context (f : x --> y) (g : y --> z).

  Let psi := f · ⟨g , identity _⟩.
  Let s := conditional psi.

  Local Lemma psi_1 : psi · proj1 = f · g.
  Proof.
    unfold psi.
    rewrite <- assoc.
    rewrite pairing_proj1.
    reflexivity.
  Qed.

  Local Lemma psi_disintegrated
       : psi = ⟨f · g · copy z, identity x⟩
               · mon_lassociator _ _ _
               · identity z #⊗ s.
  Proof. 
    unfold s.
    pose(w := conditional_eq psi).
    rewrite psi_1 in w.
    exact w.
  Qed.

  Local Lemma causality_rewrite_lemma {w : C} (h : z --> w) :
      f · ⟨g · ⟨h, identity _⟩, identity _⟩ 
    = ⟨ f · (g · ⟨h, identity _⟩) · (identity _ #⊗ copy _) , identity x ⟩ 
      · (mon_rassociator _ _ _) #⊗ identity x
      · mon_lassociator _ _ _
      · identity _ #⊗ s.
  Proof.
    transitivity (⟨f · g · copy z, identity x⟩
               · mon_lassociator _ _ _
               · identity z #⊗ s
               · ⟨h, identity _⟩ #⊗ identity _).
    { etrans. {
        rewrite <- pairing_tensor_l.
        rewrite assoc.
        assert(aux : f · ⟨ g, identity y ⟩ = psi). { reflexivity. }
        rewrite aux.
        rewrite psi_disintegrated.
        reflexivity. }
      reflexivity. }

    etrans. {
      rewrite assoc'.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite assoc.
      reflexivity. }

    apply maponpaths_2.

    etrans. {
      rewrite assoc'.
      rewrite <- tensor_id_id.
      rewrite <- tensor_lassociator.
      rewrite assoc.
      reflexivity. }

    apply maponpaths_2.

    rewrite !pairing_tensor_l.

    apply (maponpaths (λ expr, ⟨expr, identity x⟩)).

    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite assoc.
    rewrite <- pairing_id.
    rewrite !pairing_tensor.
    rewrite !id_left, !id_right.    
    rewrite pairing_rassociator.
    reflexivity.
  Qed.
  
  Local Lemma causality_conclusion {w : C} (h1 h2 : z --> w) 
            (e : f · (g · ⟨h1, identity _⟩) = f · (g · ⟨h2, identity _⟩)) :
      f · ⟨g · ⟨h1, identity _⟩, identity _⟩ 
    = f · ⟨g · ⟨h2, identity _⟩, identity _⟩.
  Proof.
    rewrite! causality_rewrite_lemma.
    rewrite e.
    reflexivity.
  Qed.
  
End ConditionalsImplyCausalityLemmas.

(* Corollaries *)

Theorem conditionals_imply_causality {C : markov_category_with_conditionals} : is_causal C.
Proof.
  apply make_causality_l.
  intros x y z w f g h1 h2.
  apply causality_conclusion.
Qed.

Proposition conditionals_imply_relative_positivity 
  (C : markov_category_with_conditionals) : is_rel_positive C.
Proof.
  apply causal_implies_rel_positive.
  apply conditionals_imply_causality.
Qed.

Theorem conditionals_imply_positivity {C : markov_category_with_conditionals} : is_positive C.
Proof.
  apply rel_positive_implies_positive.
  apply conditionals_imply_relative_positivity.
Qed.

Section ConditionalsAndRelativePositivity.
  Context {C : markov_category} 
          (rp : is_rel_positive C). 

  (* any coisometry is almost surely deterministic *)
  Proposition relpos_coisometry_lemma 
    {a x y : C} (p : a --> x) (f : x --> y) (g : y --> x)
    (bayes_inv : is_bayesian_inverse p f g)
    (inv_gf : g · f =_{p · f} identity y)
    : is_deterministic_ase p f.
  Proof.
    unfold is_deterministic_ase.

    assert(gf_det_ase : is_deterministic_ase (p · f) (g · f)).
    { apply is_deterministic_ase_stable with (identity _).
      - apply ase_symm. exact inv_gf.
      - apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity. } 

    apply make_equal_almost_surely_l.

    etrans. {
      rewrite <- pairing_tensor_l, assoc.
      rewrite (is_bayesian_inverse_r _ _ _ bayes_inv).
      rewrite <- assoc, pairing_tensor_l.
      rewrite id_left.
      rewrite <- pairing_id.
      reflexivity.
    }

    rewrite <- pairing_eq.
    apply cancel_pairing_lassociator.

    symmetry.
    etrans. {
      rewrite pairing_split_r, assoc.
      rewrite (is_bayesian_inverse_r _ _ _ bayes_inv).
      rewrite assoc', pairing_tensor_r.
      reflexivity.
    }
    symmetry.           

    apply equal_almost_surely_r.

    apply ase_trans with (⟨ g · f , g ⟩).
    { apply ase_pairing_l.
      apply ase_symm.
      exact inv_gf. }
    
    apply ase_symm.
    apply rel_positivity_l.
    - exact rp.
    - exact gf_det_ase.
  Qed. 

  (* If f, g are a section-retraction pair, then they are each others's Bayesian inverses *)
  Proposition splitting_to_bayesian_inverse 
    {a x y : C} (p : a --> x) (f : x --> y) (g : y --> x)
    : (f · g =_{p} identity x) -> is_bayesian_inverse p f g.
  Proof. 
    intros inv_fg.
    apply make_bayesian_inverse_r.
    rewrite <- assoc.
    apply equal_almost_surely_composition.
    apply ase_trans with ⟨f, f · g⟩.
      { apply ase_pairing_r.
        apply ase_symm.
        exact inv_fg. }
    apply ase_symm.
    apply rel_positivity_r.
      - exact rp.
      - apply is_deterministic_ase_stable with (identity _).
        apply ase_symm. exact inv_fg.
        apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity.
  Qed.
  
End ConditionalsAndRelativePositivity.