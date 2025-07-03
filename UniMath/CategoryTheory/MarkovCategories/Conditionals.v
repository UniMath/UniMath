(*********************************************
Conditionals

We define the notion of a Markov category with chosen conditionals,
and various interderivable notions such as Bayesian inverses. We prove
various consequences of the existence of conditionals for information flow axioms.

1. Definition of [markov_category_with_conditionals]
2. Accessors
   - Specialized definitions and lemmas for conditional distributions
3. Bayesian Inverses
   - Definition of the Bayesian inverse (dagger)
   - Every Markov category with conditonals comes with a 
     canonical choice of Bayesian inverse
4. Consequences and derived Information Flow Axioms
   - Every Markov category with conditionals is causal
   - Every Markov category with conditionals is positive
5. The Dagger Structure of Bayesian Inverses

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

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** * 1. Definition of [markov_category_with_conditionals] *)

Section DefConditionals.
  Context {C : markov_category}.

  Definition is_conditional {a x y : C} (f : a --> x ⊗ y) (k : x ⊗ a --> y) : UU
    := f = copy a 
           · (f · proj1 · copy x) #⊗ identity a
           · mon_lassociator _ _ _
           · identity x #⊗ k.

End DefConditionals.

Definition has_conditionals (C : markov_category) : UU :=
   ∏ (a x y : C) (f : a --> x ⊗ y),
   ∑ (k : x ⊗ a --> y), is_conditional f k.

Definition markov_category_with_conditionals : UU :=
   ∑ (C : markov_category), has_conditionals C. 

Coercion markov_cat_with_conditional_to_markov
         (C : markov_category_with_conditionals)
  : markov_category := pr1 C.

(** * 2. Accessors *)

Section Accessors.
  Context {C : markov_category_with_conditionals}.

  Definition conditional {a x y : C} (f : a --> x ⊗ y) : x ⊗ a --> y
    := pr1 (pr2 C a x y f).

  Proposition conditional_eq {a x y : C} (f : a --> x ⊗ y)
    : f = copy a 
           · (f · proj1 · copy x) #⊗ identity a
           · mon_lassociator _ _ _
           · identity x #⊗ (conditional f).
  Proof.
    exact (pr2 (pr2 C a x y f)).
  Qed.
End Accessors.

Lemma copy_tensor_x_I_mor_comp {C : markov_category} {x y : C} (f : I_{C} --> x ⊗ x) (g : x ⊗ I_{C} --> y) : 
     ⟨f, identity _⟩ · mon_lassociator _ _ _ · (identity _ #⊗ g) 
   = f · (identity _ #⊗ (mon_rinvunitor _ · g)).
Proof.
  unfold pairing.
  rewrite copy_I_mon_rinvunitor.
  rewrite <- tensor_rinvunitor.
  rewrite <- !assoc.
  apply maponpaths.
  rewrite <- mon_rinvunitor_triangle.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite assoc.
    rewrite mon_rassociator_lassociator.
    apply id_left.
  }
  rewrite <- tensor_comp_l_id_r.
  apply idpath.
Qed.

Section ConditionalDistributions.
  Context {C : markov_category_with_conditionals}.

  Definition conditional_distribution_1 {x y : C} (p : I_{C} --> x ⊗ y) : x --> y
    := mon_rinvunitor _ · conditional p.

  Definition conditional_distribution_2 {x y : C} (p : I_{C} --> x ⊗ y) : y --> x
    := conditional_distribution_1 (p · sym_mon_braiding _ _ _). 

  Notation "p |1" := (conditional_distribution_1 p) : markov.
  Notation "p |2" := (conditional_distribution_2 p) : markov.
 
  Proposition conditional_distribution_1_eq {x y : C} (p : I_{C} --> x ⊗ y) :
    p = p · proj1 · ⟨identity x, p|1⟩.
  Proof.
    unfold conditional_distribution_1. 
    etrans. { apply (conditional_eq p). }
    rewrite <- pairing_eq.
    rewrite copy_tensor_x_I_mor_comp.
    unfold pairing.
    rewrite assoc.
    reflexivity.
  Qed.

  Proposition conditional_distribution_2_eq {x y : C} (p : I_{C} --> x ⊗ y) :
    p = p · proj2 · ⟨p|2, identity y⟩.
  Proof.
    apply cancel_braiding.
    unfold conditional_distribution_2.
    etrans.
    {
      apply conditional_distribution_1_eq.
    }
    refine (!_).
    do 2 refine (assoc' _ _ _ @ _).
    rewrite pairing_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ assoc' _ _ _).
    apply maponpaths_2.
    rewrite sym_mon_braiding_proj1.
    reflexivity.
  Qed.

  Proposition conditional_distribution_1_ase_unique {x y : C} (p : I_{C} --> x ⊗ y) (f : x --> y) :
    p = p · proj1 · ⟨identity x, f⟩ -> f =_{p · proj1} p|1.
  Proof.
    intros e.
    unfold equal_almost_surely.
    rewrite <- conditional_distribution_1_eq.
    rewrite <- e.
    reflexivity.
  Qed.

  Proposition conditional_distribution_2_ase_unique {x y : C} (p : I_{C} --> x ⊗ y) (f : y --> x) :
    p = p · proj2 · ⟨f, identity y⟩ -> f =_{p · proj2} p|2.
  Proof.
    intros e.
    unfold equal_almost_surely.
    apply cancel_braiding.
    rewrite !assoc'.
    rewrite !pairing_sym_mon_braiding.
    rewrite !assoc.
    rewrite <- conditional_distribution_2_eq.
    rewrite <- e.
    reflexivity.
  Qed.

End ConditionalDistributions.

Notation "p |1" := (conditional_distribution_1 p) : markov.
Notation "p |2" := (conditional_distribution_2 p) : markov.

(** * 3. Bayesian inverses *)

Section DefBayesianInverse.
  Context {C : markov_category}.
  
  Definition is_bayesian_inverse {x y : C} (p : I_{C} --> x) (f : x --> y) (fi : y --> x) : UU
    := p · ⟨identity x, f⟩ = (p · f) · ⟨fi, identity y⟩.

  Definition bayesian_inverse_ase_unique {x y : C} (p : I_{C} --> x) (f : x --> y) (g1 g2 : y --> x)
                                         (b1 : is_bayesian_inverse p f g1) (b2 : is_bayesian_inverse p f g2) :
    g1 =_{p · f} g2.
  Proof.
    unfold is_bayesian_inverse in *.
    apply pairing_flip.
    rewrite <- b1, <- b2.
    reflexivity.
  Qed.
    
End DefBayesianInverse.

Section ConstructionBayesianInverse.
  Context {C : markov_category_with_conditionals}.
  Context {x : C}.
  Context (p : I_{C} --> x).

  Definition bayesian_inverse {y : C} (f : x --> y) : y --> x
    := mon_rinvunitor y · conditional (p · ⟨f, identity x⟩).

  Definition bayesian_inverse_eq {y : C} {f : x --> y} :
    is_bayesian_inverse p f (bayesian_inverse f).
  Proof.
    unfold is_bayesian_inverse, bayesian_inverse.
    apply pairing_flip.
    pose(phi := p · ⟨ f, identity x ⟩).
    pose(K := conditional_eq phi).
    
    assert(Aux1 : phi · proj1 = p · f).
    { unfold phi. 
      rewrite <- assoc.
      rewrite pairing_proj1.
      reflexivity. }
    rewrite Aux1 in K.
    clear Aux1.
    rewrite <- pairing_eq in K.
    rewrite copy_tensor_x_I_mor_comp in K.
    unfold phi in K.
    rewrite <- assoc in K.
    etrans. 
    { rewrite K. reflexivity. }
    reflexivity.
  Qed.

  Proposition bayesian_inverse_eq_l {y : C} (f : x --> y) :
    p · f · ⟨bayesian_inverse f, identity _⟩ = p · ⟨identity _, f⟩.
  Proof.
    symmetry.
    assert(e : is_bayesian_inverse p f (bayesian_inverse f)). 
      { apply bayesian_inverse_eq. }
    unfold is_bayesian_inverse in e.
    rewrite <- e.
    reflexivity.
  Qed. 
   
  Proposition bayesian_inverse_eq_r {y : C} (f : x --> y) :
    p · f · ⟨identity _, bayesian_inverse f⟩ = p · ⟨f, identity _⟩.
  Proof.
    apply cancel_braiding.
    rewrite !assoc', !pairing_sym_mon_braiding, assoc.
    apply bayesian_inverse_eq_l.
  Qed.
      
End ConstructionBayesianInverse.

#[global] Opaque bayesian_inverse.

(** * 4. Consequences and derived information flow axioms *)

Section Lemmas.
  Context {C : markov_category_with_conditionals}.
  Context {x y z : C}.
  Context (f : x --> y) (g : y --> z).

  (* The causality and positivity proofs allow some shared setup *)

  Let psi := f · ⟨g , identity _⟩.
  Let s := conditional psi.

  Local Lemma psi_1 : psi · proj1 = f · g.
  Proof.
    unfold psi.
    rewrite <- assoc.
    rewrite pairing_proj1.
    reflexivity.
  Qed.

  Local Lemma psi_2 : psi · proj2 = f.
  Proof.
    unfold psi.
    rewrite <- assoc.
    rewrite pairing_proj2.
    rewrite id_right.
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

  Local Lemma psi_disintegrated_marginal : ⟨f · g, identity _ ⟩ · s = f.
  Proof.
    assert(A1 : f · g = f · g · ⟨identity _, identity _⟩ · proj2).
    { rewrite <- assoc.
      rewrite pairing_proj2, id_right.
      reflexivity. }
    rewrite A1.
    rewrite <- (id_left (identity x)).
    rewrite <- pairing_tensor.
    rewrite <- assoc.
    rewrite proj2_naturality.
    rewrite assoc, assoc.
    
    rewrite pairing_id.
    unfold pairing.
    rewrite <- pairing_eq.
    rewrite <- psi_disintegrated.
    rewrite psi_2.
    reflexivity.
   Qed.

  (** Lemmas for the positivity proof *)

  Local Lemma positivity_conclusion (det_fg : is_deterministic (f · g)) : psi = ⟨f · g , f⟩.
  Proof. 
    rewrite psi_disintegrated.
    rewrite det_fg.
    rewrite <- !pairing_eq.
    rewrite <- pairing_rassociator.
    transitivity (⟨ f · g, ⟨ f · g, identity x ⟩ ⟩ 
                  · (mon_rassociator z z x · mon_lassociator z z x)
                  · identity z #⊗ s).
    { rewrite assoc. reflexivity. }
    rewrite mon_rassociator_lassociator.
    rewrite id_right.
    rewrite pairing_tensor, id_right.
    rewrite psi_disintegrated_marginal.
    reflexivity.
  Qed.

  (** Lemmas for the causality proof *)

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
  
End Lemmas.

Theorem conditionals_imply_positivity {C : markov_category_with_conditionals} : is_positive C.
Proof.
  apply make_positivity_l.
  intros x y z f g d.
  apply positivity_conclusion.
  exact d.
Qed.

Theorem conditionals_imply_causality {C : markov_category_with_conditionals} : is_causal C.
Proof.
  apply make_causality_l.
  intros x y z w f g h1 h2.
  apply causality_conclusion.
Qed.

(** * 5. The Dagger Structure of Bayesian Inverses *)

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