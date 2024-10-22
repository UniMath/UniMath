(*********************************************
Conditionals

We define the notion of a Markov category with conditionals, 
interderivable notions such as Bayesian inverses, and derive various consequences,
such as the various information flow axioms.

1. Definition `markov_category_with_conditionals`
2. Accessors
3. Bayesian inverse
4. Consequences and information flow axioms

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

Lemma auxcoh {C : markov_category} {x y : C} (f : I_{C} --> x ⊗ x) (g : x ⊗ I_{C} --> y) : 
     ⟨f, identity _⟩ · mon_lassociator _ _ _ · (identity _ #⊗ g) 
   = f · (identity _ #⊗ (mon_rinvunitor _ · g)).
Proof.
  rewrite copy_I_mon_rinvunitor.
  rewrite <- tensor_rinvunitor.
  rewrite <- !assoc.
  apply maponpaths.
  (* Maybe like this? *)
  rewrite <- mon_rinvunitor_triangle.
  rewrite assoc.
  Admitted.

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

    rewrite auxcoh in K.
    unfold phi in K.
    rewrite <- assoc in K.
    etrans. 
    { rewrite K. reflexivity. }
    reflexivity.
  Qed.
      
End ConstructionBayesianInverse.

Section ConditionalsImplyPositivity.
  Context {C : markov_category_with_conditionals}.
  Context {x y z : C}.
  Context (f : x --> y) (g : y --> z).
  Context (det_fg : is_deterministic (f · g)).

  Let psi := f · ⟨g , identity _⟩.
  Let s := conditional psi.

  Lemma psi_1 : psi · proj1 = f · g.
  Proof.
    unfold psi.
    rewrite <- assoc.
    rewrite pairing_proj1.
    reflexivity.
  Qed.

  Lemma psi_2 : psi · proj2 = f.
  Proof.
    unfold psi.
    rewrite <- assoc.
    rewrite pairing_proj2.
    rewrite id_right.
    reflexivity.
  Qed.

  Lemma K : psi
            = copy x 
              · (f · g · copy z) #⊗ identity x
              · mon_lassociator _ _ _
              · identity z #⊗ s.
  Proof. 
    unfold s.
    pose(w := conditional_eq psi).
    rewrite psi_1 in w.
    exact w.
  Qed.


  Lemma Aux : ⟨f · g, identity _ ⟩ · s = f.
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
    
    assert(A2 : ⟨identity z, identity z⟩ = copy z). 
    { rewrite tensor_id_id, id_right. reflexivity. }
    rewrite A2.
    rewrite <- K.
    rewrite psi_2.
    reflexivity.
   Qed.     

  Lemma pos_flipped : psi = ⟨f · g , f⟩.
  Proof. 
    rewrite K.
    rewrite det_fg.
    rewrite <- pairing_rassociator.
    transitivity (⟨ f · g, ⟨ f · g, identity x ⟩ ⟩ 
                  · (mon_rassociator z z x · mon_lassociator z z x)
                  · identity z #⊗ s).
    { rewrite assoc. reflexivity. }
    rewrite mon_rassociator_lassociator.
    rewrite id_right.
    rewrite pairing_tensor, id_right.
    rewrite Aux.
    reflexivity.
  Qed.
    
  Proposition pos : f · ⟨identity y , g⟩ = ⟨f , f · g⟩.
  Proof.
    apply cancel_braiding.
    rewrite <- assoc, !pairing_sym_mon_braiding.
    apply pos_flipped.
  Qed.
  
End ConditionalsImplyPositivity.

Theorem conditionals_imply_positivity {C : markov_category_with_conditionals} : is_positive C.
Proof.
  unfold is_positive.
  intros x y z f g d.
  apply pos.
  exact d.
Qed.