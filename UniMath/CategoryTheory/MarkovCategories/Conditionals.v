(*********************************************
Conditionals

We define the notion of a Markov category with conditionals, 
interderivable notions such as Bayesian inverses, and derive various consequences,
such as the various information flow axioms.

1. Definition `markov_category_with_conditionals`
2. Accessors
3. Bayesian inverse
4. Consequences and derived information flow axioms

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

(* TODO this already gets used twice, so it could be an interesting named lemma *)
Lemma auxcoh {C : markov_category} {x y : C} (f : I_{C} --> x ⊗ x) (g : x ⊗ I_{C} --> y) : 
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

  Notation "p |1" := (conditional_distribution_1 p).
  Notation "p |2" := (conditional_distribution_2 p).

  Proposition conditional_distribution_1_eq {x y : C} (p : I_{C} --> x ⊗ y) :
    p = p · proj1 · ⟨identity x, p|1⟩.
  Proof.
    unfold conditional_distribution_1. 
    etrans. { apply (conditional_eq p). }
    rewrite <- pairing_eq.
    rewrite auxcoh.
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

End ConditionalDistributions.

Notation "p |1" := (conditional_distribution_1 p).
Notation "p |2" := (conditional_distribution_2 p).

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
    rewrite auxcoh in K.
    unfold phi in K.
    rewrite <- assoc in K.
    etrans. 
    { rewrite K. reflexivity. }
    reflexivity.
  Qed.
      
End ConstructionBayesianInverse.

#[global] Opaque bayesian_inverse.

Section Couplings.
  Context {C : markov_category_with_conditionals}.

  (* 
    Formally, the composition of couplings β and γ is only meaningful  
    if the codomain of β equals the domain of γ. 
    So it would make sense to add an extra argument
      `e : β · proj2 = γ · proj1`
    encoding this constraint to this definition.
    However, we chose to leave this out this `e` for convenience, 
    because the (opaque) definition of `coupling_composition` makes sense regardless, 
    and carrying around the proof `e` makes lemmas about `coupling_composition` harder to write.

    However, we will need the assumption `e` for the equivalent characterizations
    `coupling_composition_eq1`,`coupling_composition_eq12,`coupling_composition_eq3`.
    
  *)
  Definition coupling_composition {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          : I_{C} --> x ⊗ z := β · proj2 · ⟨ β|2 , γ|1 ⟩.

  Proposition coupling_composition_eq {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = β · proj2 · ⟨ β|2 , γ|1 ⟩.
  Proof. 
    reflexivity.
  Qed.

  Proposition coupling_composition_eq2 {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = β · (identity _ #⊗ γ|1).
  Proof. 
    unfold coupling_composition.
    rewrite pairing_split_l.
    rewrite assoc.
    apply maponpaths_2.
    rewrite <- conditional_distribution_2_eq.
    reflexivity.
  Qed.   

  Proposition coupling_composition_eq3 {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = γ · (β|2 #⊗ identity _).
  Proof. 
    unfold coupling_composition.
    rewrite pairing_split_r.
    rewrite assoc.
    apply maponpaths_2.
    rewrite e.
    rewrite <- conditional_distribution_1_eq.
    reflexivity.
  Qed.

  Proposition coupling_composition_dom {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) :
    coupling_composition β γ · proj1 = β · proj1.
  Proof.
    rewrite coupling_composition_eq2 ; [ | assumption ].
    rewrite assoc'.
    rewrite proj1_tensor.
    reflexivity.
  Qed.

  Proposition coupling_composition_cod {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) :
    coupling_composition β γ · proj2 = γ · proj2.
  Proof.
    rewrite coupling_composition_eq3 ; [ | assumption ].
    rewrite assoc'.
    rewrite proj2_tensor.
    reflexivity.
  Qed.
    
  Definition identity_coupling {x : C} (p : I_{C} --> x) : I_{C} --> x ⊗ x := p · copy x.

  Proposition identity_coupling_dom {x : C} (p : I_{C} --> x) : identity_coupling p · proj1 = p.
  Proof.
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite copy_proj1.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition identity_coupling_cod {x : C} (p : I_{C} --> x) : identity_coupling p · proj2 = p.
  Proof.
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite copy_proj2.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition coupling_id_left {x y : C} (p : I_{C} --> x) (β : I_{C} --> x ⊗ y) 
      (e : identity_coupling p · proj2 = β · proj1) : 
    coupling_composition (identity_coupling p) β = β.
  Proof.
    assert (e2 : p = β · proj1).
    { rewrite <- e. rewrite identity_coupling_cod. reflexivity. }
    rewrite coupling_composition_eq2 ; [ | assumption ].
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite e2.
    rewrite conditional_distribution_1_eq.
    reflexivity.
  Qed.

  Proposition coupling_id_right {x y : C} (p : I_{C} --> y) (β : I_{C} --> x ⊗ y) 
      (e : β · proj2 = identity_coupling p · proj1) : 
    coupling_composition β (identity_coupling p) = β.
  Proof.
    assert (e2 : p = β · proj2).
    { rewrite e. rewrite identity_coupling_dom. reflexivity. }
    rewrite coupling_composition_eq3 ; [ | assumption ].
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite e2.
    rewrite conditional_distribution_2_eq.
    reflexivity.
  Qed.

  (* TODO serious name *)
  Proposition aux42 {x y x' y' : C}
    (β : I_{C} --> x ⊗ y)
    (f : x --> x') (g : y --> y') :
   β · proj1 · ⟨ f , β|1 · g ⟩ = β · proj2 · ⟨ β|2 · f, g ⟩.
  Proof.
    rewrite <- (id_left f).
    rewrite <- pairing_tensor.
    rewrite assoc.
    rewrite <- conditional_distribution_1_eq.
    rewrite id_left.
    rewrite <- (id_left g).
    rewrite <- pairing_tensor.
    rewrite assoc.
    rewrite <- conditional_distribution_2_eq.
    rewrite id_left.
    reflexivity.
  Qed.

  Proposition coupling_composition_assoc {x y z w : C} 
    (β : I_{C} --> x ⊗ y)
    (γ : I_{C} --> y ⊗ z)
    (δ : I_{C} --> z ⊗ w)
    (e1 : β · proj2 = γ · proj1)
    (e2 : γ · proj2 = δ · proj1)
    : coupling_composition (coupling_composition β γ) δ
      =
      coupling_composition β (coupling_composition γ δ).
  Proof.
    assert (coupling_composition β γ · proj2 = δ · proj1) as e3.
    { rewrite coupling_composition_cod ; assumption. }
    assert (β · proj2 = coupling_composition γ δ · proj1) as e4.
    { rewrite coupling_composition_dom ; assumption. }

    etrans.
    {
      repeat (rewrite coupling_composition_eq2 ; [ | assumption ]).
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (conditional_distribution_1_eq β).
      }
      do 2 refine (assoc' _ _ _ @ _).
      rewrite <- tensor_comp_id_l.
      rewrite pairing_tensor_l.
      rewrite aux42.
      rewrite e1.
      rewrite aux42.
      rewrite e2.
      rewrite <- (id_right (δ |1)).
      rewrite aux42.
      rewrite id_right.
      rewrite <- pairing_tensor_r.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (!(conditional_distribution_2_eq δ)).
    }
    repeat (rewrite coupling_composition_eq3 ; [ | assumption ]).
    rewrite tensor_comp_id_r.
    rewrite assoc'.
    reflexivity.
  Qed.

End Couplings.

#[global] Opaque coupling_composition.

(* TODO Clean this up *)
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

  Local Lemma Aux : ⟨f · g, identity _ ⟩ · s = f.
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
    rewrite <- K.
    rewrite psi_2.
    reflexivity.
   Qed.

  Lemma pos_flipped : psi = ⟨f · g , f⟩.
  Proof. 
    rewrite K.
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

Theorem conditionals_imply_causality {C : markov_category_with_conditionals} : is_causal C.
Proof.
  (* TODO Theorem 11.34 in [Fritz] *)
Abort.